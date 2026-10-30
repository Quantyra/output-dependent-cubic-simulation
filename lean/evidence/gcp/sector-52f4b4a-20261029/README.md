# GCP baseline timeout receipt

The archived run targeted manuscript repository commit `52f4b4aa6e97cc076c6de7623ac5c5efbefbb69d` on the already-running shared `quantyra-lean-builder-01`, project `quantyra-lean-cert-20260915`, zone `us-central1-a`. The exact source Git archive had SHA-256 `3df95c49cef60aba3af06c94c6b73b3298ae8d943b572dfdcdda9e76ad78f9e2`; the runner verified it and all pinned dependency revisions. The recorded compiler was Lean 4.30.0 commit `d024af099ca4bf2c86f649261ebf59565dc8c622`.

`baseline-timeout-evidence.tar` has SHA-256 `c381d52ed22226ddc0828ae355c3d915ab2aa620005bfcd76a358dadff9eaae4`, matching the remote archive. It contains the original runner, launcher and build streams, compiler version and toolchain hashes, and terminal `exit-code`. The exit code is **124**: the build stage exceeded its 1800-second limit. The last captured build line was job 1875; `build.stderr` was empty. The build did not complete, and the audit and finite examples were not run. Partial compiled artifacts are not a passing build or proof receipt.

A separate continuation may reuse the task-owned partial cache only after checking the terminal timeout, source/dependency/toolchain identities and absence of other shared Lean/Lake processes. It must preserve this failed attempt and record its own outcome. No labeled manuscript theorem is certified by this receipt.
