#!/usr/bin/env python3
"""Stable RED fingerprinting for the certification pipeline."""
import argparse, hashlib, json, re, sys
from datetime import datetime, timezone
from pathlib import Path

SCHEMA_VERSION = 1
NORMALIZERS = [
    (re.compile(r"\b[0-9a-f]{40}\b"), "<SHA>"),
    (re.compile(r"\b[0-9a-f]{7,12}\b"), "<SHORT_SHA>"),
    (re.compile(r"\d{4}-\d{2}-\d{2}[T ]\d{2}:\d{2}:\d{2}(\.\d+)?Z?"), "<TS>"),
    (re.compile(r"/(home|Users|runner|tmp|var)/[^\s:]+"), "<PATH>"),
    (re.compile(r":\d+:\d+"), ":<LINE>:<COL>"),
    (re.compile(r"\bline \d+\b"), "line <N>"),
    (re.compile(r"\b(run|job)[-_ ]?(id)?[: ]?\d{6,}\b", re.I), r"\1 <ID>"),
    (re.compile(r"\b[0-9a-f]{16,}\b"), "<HEX>"),
    (re.compile(r"[ \t]+"), " "),
]

def normalize(message):
    out = message
    for pattern, repl in NORMALIZERS:
        out = pattern.sub(repl, out)
    return out.strip()

def classify(message):
    m = message.lower()
    if "type mismatch" in m: return "TYPE_MISMATCH"
    if "unknown identifier" in m or "unknown constant" in m or "invalid field" in m and "environment does not contain" in m: return "UNKNOWN_IDENT"
    if "failed to synthesize" in m or ("instance" in m and "not found" in m): return "INSTANCE_MISSING"
    if "unsolved goals" in m: return "UNSOLVED_GOALS"
    if "declaration uses 'sorry'" in m or "sorry" in m: return "SORRY"
    if "timeout" in m or "timed out" in m: return "TIMEOUT"
    if "import" in m and ("not found" in m or "failed" in m): return "IMPORT_FAIL"
    if "permission denied" in m or "no such file" in m: return "IO_ERROR"
    return "OTHER"

def error_hash(message_normalized):
    return hashlib.sha256(message_normalized.encode()).hexdigest()[:16]

def extract_failed_steps(log):
    # GitHub Actions/Lean: retain only diagnostic payload, not generic runner noise.
    diagnostic = []
    for ln in log.splitlines():
        if re.search(r"(^|\s)(error:|✖)|type mismatch|unknown (identifier|constant|tactic)|invalid field|unsolved goals|failed to synthesize", ln, re.I):
            diagnostic.append(ln)
    if not diagnostic:
        return []
    raw = "\n".join(diagnostic[:40])
    norm = normalize(raw)
    return [{"name":"lean-build","error_class":classify(raw),"error_hash":error_hash(norm),"message_raw":raw[:4000],"message_normalized":norm[:4000]}]

def find_match(red_dir, eh, exclude_sha=None):
    for f in sorted(Path(red_dir).glob("*.json")):
        try: e=json.loads(f.read_text())
        except Exception: continue
        if exclude_sha and e.get("sha")==exclude_sha: continue
        if any(s.get("error_hash")==eh for s in e.get("failed_steps",[])): return e
    return None

def cmd_record(a):
    log=Path(a.log_file).read_text(errors="replace"); rd=Path(a.red_dir); rd.mkdir(parents=True,exist_ok=True)
    failed=extract_failed_steps(log); primary=failed[0] if failed else None
    match=find_match(rd,primary["error_hash"],a.sha) if primary else None
    entry={"schema_version":SCHEMA_VERSION,"sha":a.sha,"repo":a.repo,"workflow":a.workflow or "","run_id":a.run_id,"job_id":a.job_id,"ref":a.ref or "","timestamp_utc":datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),"conclusion":"failure","failed_steps":failed,"files_touched":a.files or [],"log_url":a.log_url or "","log_sha256":hashlib.sha256(log.encode()).hexdigest(),"previous_red_match":{"matched":bool(match),"sha":match.get("sha") if match else None,"error_hash":primary["error_hash"] if match else None},"fix":{"sha":None,"status":"PENDING","note":""}}
    out=rd/f"{a.sha}.json"; out.write_text(json.dumps(entry,indent=2,ensure_ascii=False)+"\n"); print(f"[record] {out}")
    if match: print(f"[record] RECURRENCE {primary['error_hash']} from {match['sha']}")
    return 0 if failed else 2

def cmd_check(a):
    failed=extract_failed_steps(Path(a.log_file).read_text(errors="replace"))
    if not failed: print("[check] no failure extracted"); return 2
    hit=False
    for s in failed:
        m=find_match(Path(a.red_dir),s["error_hash"]); hit |= bool(m)
        print(f"[check] {'RECURRENCE' if m else 'NEW'}: {s['error_class']} ({s['error_hash']})" + (f" seen at {m['sha']}" if m else ""))
    return 1 if hit else 0

def main():
    p=argparse.ArgumentParser(); sub=p.add_subparsers(dest="cmd",required=True)
    r=sub.add_parser("record"); r.add_argument("sha"); r.add_argument("log_file"); r.add_argument("red_dir"); r.add_argument("repo"); r.add_argument("--run-id",type=int); r.add_argument("--job-id",type=int); r.add_argument("--workflow"); r.add_argument("--ref"); r.add_argument("--log-url"); r.add_argument("--files",nargs="*"); r.set_defaults(func=cmd_record)
    c=sub.add_parser("check"); c.add_argument("log_file"); c.add_argument("red_dir"); c.set_defaults(func=cmd_check)
    a=p.parse_args(); sys.exit(a.func(a))
if __name__=="__main__": main()
