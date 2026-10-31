# GCP certification evidence: linear residual-character map

Source/audit commit: `6ca49ab58cc2d574fbc0bedeff1b693d625c1ae8`.

The exact Lean source archive is `sector-6ca49ab-source.tar` (SHA-256 `d56e68a5cf650ae1529a2cde7e3f9409b65af970073f7cd7f1fdc984ebadfd97`, 1,423,360 bytes). It contains tracked Lean sources and the exact audit checker, excluding prior evidence archives; its hash was checked on the dedicated builder.

The dedicated Google Cloud builder `quantyra-sector-lean-builder-02` used Lean 4.30.0, commit `d024af099ca4bf2c86f649261ebf59565dc8c622`, and pinned Lake manifest SHA-256 `ab0911ef870c1e4193db513c9766a9be167085f6222f4381f7a2aae4a0094642`. Full `lake build` completed (2,175 jobs). Integrated `Audit.lean` and exact expected-axiom checker passed.

`recordedResidualLinearPart_vectorXor` and `recordedResidualLinearPart_zeroVector` establish that the generated residual-character map is linear over the finite Boolean vector space. Both use only `propext` and `Quot.sound`.

This makes the earlier support-fiber result a fiber of a proved linear map. The remaining task is to identify its kernel with the image of the source quadratic polar form and prove the rank/support-origin statements. No normalized sector identity, boundedness/cost result, or labeled paper theorem is certified here.
