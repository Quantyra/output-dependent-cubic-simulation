# Semantic contract for the published target

Status: design contract, not formal declarations or a proof. It fixes what later Lean statements must mean and what must be shown about the implementation. The published PDF, not this document, controls the target.

## Source and circuit

For each natural `n >= 1`, let `V` be the functions from `Fin n` to the two-element field. A source consists of a symmetric invertible linear map `J : V -> V`, two square-free Boolean ANFs `f0, f1` of degree at most three including the constant monomial, a basis input `beta : V`, and an output index `i : Fin n`. A descriptor is a finite byte encoding of these objects, with an explicit decoding relation. A native source is the complete gate sequence with the identity header encoding that descriptor and the canonical body produced from it. Recognition must decode, validate, recompile and compare the whole sequence and boundary values. An arbitrary equivalent circuit is not admitted merely by denotational equality.

Define `F_J` by entries `2^(-n/2) (-1)^(x dot J y)`, phase `D_f` by `(-1)^f(x)`, and output projection by `x_i = 1`. Prove that the native gate denotation equals `F_J D_f1 F_J D_f0 F_J |beta>` including global-phase behavior, and that the output probability is the squared norm of its projection. The descriptor and gate compilation are algorithms over finite data; they must not be replaced by a hypothesis that the output probability or a useful decomposition is supplied.

## Sector construction

Define `e` as the one-hot vector at `i`, `j = J^-1 e`, and `Q(v) = f1(v) + f1(v+j)` in the two-element field. Define the alternating polar form and Walsh transform of `Q`, then construct the even rank `r`, affine support `J(d0+S)`, basis `D`, annihilator `C`, right inverse `R`, matching offset `eta = C d0`, and `s` satisfying `D s = d0 + R eta`. All objects must be computable from the source, including `r = 0`, `c = n-r = 0`, nonzero input and affine-origin cases.

For each sector `a`, define `psi_a(y) = 2^(-r/2) (-1)^(f0(Ra+Dy)+(J beta) dot (Ra+Dy))`. Derive its unit norm and the exact mass `2^-c` in the unconditioned state. Define the pulled-back output observable from the literal circuit and derive its Clifford form, the flat kernel with its quadratic sign, coset matching, real overlap `X_a`, `|X_a| <= 1`, `X_a = X_(a+eta)`, and `1-2p = average_a X_a`. No sector access, Clifford action, normalization oracle or desired overlap bound is an assumption on the source.

## Discovery and finite randomness

The tensor is the third Boolean difference of `f0` restricted to `S`. A verified control space `U` has dimension `k <= q` and kernel `K` satisfying `T(K,K,K)=0`. Model the zero-tensor and one-control shortcuts as deterministic; the scanned two-form basis shortcut is sound but not complete. The randomized branch has a finite tape of independent fair bits, at most `A_q = 4^q(h+2)` probes, at most `C_q = 4(q+1)2^(q^2)` candidate subspaces per image, a full verification of every accepted candidate, high-rank skips, and explicit refusals.

The discovery success theorem must quantify over every source with an actual certificate and an anchor `v in K` of contraction rank `2k`, with failure at most `2^(-h-1)`. Certificate existence alone is not the promise. A candidate-budget truncation is a refusal without that success guarantee. Soundness is unconditional for each accepted certificate. Establish nonvacuity with actual admitted sources, including the published determinant family; do not assume a certificate or an estimator as an input oracle.

## Norm estimator and output

For a discovered frame, construct the stabilizer branches and `O_a` from the source; define `u_a = psi_(a+eta) + O_a psi_a`. Sample matching-orbit representatives uniformly and independently sample `d_j` uniformly in `Z/4Z` and `a_jl` as fair bits for the paper's equatorial phase. The random variable is `Y = 2^r |<phi_A,u_a>|^2 / 2 - 1`. Prove its expectation and variance using the explicit finite distribution, including zero norm. Individual `Y` is unbounded and must not be clipped.

The readout uses `L = 32*4^b`, `K = 2h+3`, and `N = LK` independent joint draws for integers `b,h >= 1`. Each group mean is exact, the median is converted to `(1-median)/2`, the final probability is projected to `[0,1]`, and the result is rounded downward at `b+2` fractional bits. Show the published `3*2^(-b)/4` accuracy, failure allocation, sound conditioning on any randomly discovered accepted frame and pre-draw budget refusals. Separate the exact quadratic shortcut.

## Bit-cost model and trust boundary

Give executable small-step or otherwise justified operational semantics over finite encodings and a cost trace for parsing/replay, elimination, tensor and phase substitution, candidate enumeration, random-bit draws, real quadratic Gauss sums, integer arithmetic, accumulation and rounding. Track source size `B`, dimensions `n,r`, cap `q`, precision `b`, confidence `h`, sample count, peak storage and bit widths. Prove the paper's conservative displayed upper bounds for every random tape and the exact shortcut; state any machine-model conversion. Big-O notation without a verified bound connecting these operations to source-level algorithms does not close the resource theorem.

The intended trusted axiom baseline is `propext`, `Classical.choice`, `Quot.sound`; `sorryAx`, additional project axioms and native-evaluation trust are not accepted as a proof. Inspect elaborated declarations and `#print axioms` transitively. A finite sample check, successful build, DOI, or proof of a helper alone is not manuscript certification. Formal equivalence to Python execution requires a separate refinement bridge and is not presently asserted.
