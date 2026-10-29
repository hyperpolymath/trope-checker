#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Exercise the publisher's actual source-verification step with mocked GitHub API responses.
set -euo pipefail
root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
export RUNNER_TEMP="$work" GITHUB_REPOSITORY='owner/repo' GITHUB_EVENT_PATH="$work/event.json"
export GITHUB_OUTPUT="$work/output" MOCK_DIR="$work"
printf '%s\n' '{"workflow_run":{"id":17,"head_sha":"abc","run_attempt":1},"repository":{"full_name":"owner/repo"}}' > "$GITHUB_EVENT_PATH"
printf '%s\n' 'uses: owner/canon/.github/workflows/scan.yml@123' > "$work/trusted.yml"
cp "$work/trusted.yml" "$work/head.yml"
mkdir "$work/bin"
cat > "$work/bin/gh" <<'MOCK'
#!/usr/bin/env bash
set -euo pipefail
case "$*" in
  *'actions/workflows/fork-governance.yml'*) echo 8 ;;
  *'actions/runs/17/jobs?'*) echo '[{"jobs":[{"name":"DEED syntax / lint","conclusion":"success"},{"name":"K9-DEED conformance / validate","conclusion":"success"},{"name":"Hypatia verdict grid / Hypatia Neurosymbolic Analysis","conclusion":"success"}]}]' ;;
  *'actions/runs/17'*) echo '{"workflow_id":8,"event":"pull_request","status":"completed","repository":{"full_name":"owner/repo"},"head_sha":"abc","run_attempt":1,"referenced_workflows":[{"path":"owner/canon/.github/workflows/scan.yml@123"}]}' ;;
  *'commits/abc/pulls'*) echo '[[{"number":12,"state":"open","head":{"sha":"abc"},"base":{"repo":{"full_name":"owner/repo"}}}]]' ;;
  *'pulls/12'*) echo '{"state":"open","head":{"sha":"abc","repo":{"full_name":"owner/fork"}},"base":{"sha":"def"}}' ;;
  *'repos/owner/fork/contents/'*) base64 -w0 "$MOCK_DIR/head.yml" ;;
  *'repos/owner/repo/contents/'*) base64 -w0 "$MOCK_DIR/trusted.yml" ;;
  *) echo "unexpected gh call: $*" >&2; exit 1 ;;
esac
MOCK
chmod +x "$work/bin/gh"
export PATH="$work/bin:$PATH"
# Copy the YAML block itself, rather than a second implementation of the check.
python3 - "$root/.github/workflows/fork-governance-publish.yml" > "$work/source.sh" <<'PY'
import sys
text = open(sys.argv[1]).read()
step = text.split('      - name: Verify the source run and current pull request\n', 1)[1]
script = step.split('        run: |\n', 1)[1].split('\n      - name:', 1)[0]
print('\n'.join(line[10:] if line.startswith('          ') else line for line in script.splitlines()))
PY
bash "$work/source.sh"
printf '%s\n' 'uses: owner/canon/.github/workflows/scan.yml@123' '# attacker adds forged jobs' > "$work/head.yml"
if bash "$work/source.sh" >/dev/null 2>&1; then
  echo 'FAIL: PR-modified workflow was accepted' >&2
  exit 1
fi
echo 'PASS: publisher rejects PR-modified scan workflows even when reusable pins match'
