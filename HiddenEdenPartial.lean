import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Hidden Kuznetsov–Eden: PARTIAL formalization, not a resolution

Target toolchain: leanprover/lean4:v4.33.1
Mathlib commit: 0df444a360eaa60ab8c11dca51a86af692955474

This file proves analytic consequences of the proposed integral formula.
It does NOT construct the vector field, prove existence of a hidden attractor,
or identify this formula with singular-value Lyapunov dimension.
The entire preceding informal argument is preserved in the final comment.
Comments are not checked proofs. No unproved theorem is introduced as an axiom.

Outstanding formal work includes the cat-map suspension and exact metric,
the aperiodic invariant subset, smooth zero-set construction, smooth Nash
embedding, normal-bundle ODE and its ambient derivative, global extension,
hiddenness, and the singular-value definition and dimension identification.

Reproduction in a Lake project with the toolchain and Mathlib revision above:
  lake exe cache get
  lake env lean HiddenEdenPartial.lean
-/

noncomputable section
open Set MeasureTheory

namespace HiddenEdenPartial

/-- A scalar functional, deliberately not called actual Lyapunov dimension. -/
def candidateDimension {X : Type*} (φ : ℝ → X → X) (q : X → ℝ)
    (lam t : ℝ) (x : X) : ℝ :=
  7 / 2 - (∫ s in (0 : ℝ)..t, q (φ s x)) / (lam * t)

theorem candidate_le {X : Type*} (φ : ℝ → X → X) (q : X → ℝ)
    {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t)
    (hq : ∀ x, 0 ≤ q x) (x : X) :
    candidateDimension φ q lam t x ≤ 7 / 2 := by
  have hi := intervalIntegral.integral_nonneg_of_forall (μ := volume) ht.le
    (fun s => hq (φ s x))
  have hd := div_nonneg hi (mul_pos hlam ht).le
  unfold candidateDimension
  linarith

theorem candidate_eq_on_invariant_zero_set {X : Type*}
    (φ : ℝ → X → X) (q : X → ℝ) (S : Set X)
    (hinv : ∀ s x, x ∈ S → φ s x ∈ S)
    (hzero : ∀ x ∈ S, q x = 0) (lam t : ℝ) {x : X} (hx : x ∈ S) :
    candidateDimension φ q lam t x = 7 / 2 := by
  have hz : (fun s => q (φ s x)) = fun _ : ℝ => (0 : ℝ) := by
    funext s
    exact hzero _ (hinv s x hx)
  simp [candidateDimension, hz]

theorem candidate_lt_off_zero_set {X : Type*} [TopologicalSpace X]
    (φ : ℝ → X → X) (q : X → ℝ) (S : Set X)
    (hφ : ∀ x, Continuous (fun s => φ s x)) (hφzero : ∀ x, φ 0 x = x)
    (hq : Continuous q) (hnonneg : ∀ x, 0 ≤ q x)
    (hzero : ∀ x, q x = 0 ↔ x ∈ S)
    {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t) {x : X} (hx : x ∉ S) :
    candidateDimension φ q lam t x < 7 / 2 := by
  have hqx : 0 < q x := lt_of_le_of_ne (hnonneg x)
    (Ne.symm (fun he => hx ((hzero x).mp he)))
  have hi : 0 < ∫ s in (0 : ℝ)..t, q (φ s x) := by
    apply intervalIntegral.integral_pos ht (hq.comp (hφ x)).continuousOn
    · intro s _
      exact hnonneg _
    · exact ⟨0, ⟨le_rfl, ht.le⟩, by simpa [hφzero] using hqx⟩
  have hd := div_pos hi (mul_pos hlam ht)
  unfold candidateDimension
  linarith

/-- Compact invariant sets disjoint from the zero set have a uniform gap.
No periodic-orbit existence theorem is assumed or claimed here. -/
theorem compact_invariant_gap {X : Type*} [TopologicalSpace X]
    (φ : ℝ → X → X) (q : X → ℝ) (G : Set X)
    (hφ : ∀ x, Continuous (fun s => φ s x)) (hq : Continuous q)
    (hG : IsCompact G) (hne : G.Nonempty)
    (hinv : ∀ s x, x ∈ G → φ s x ∈ G)
    (hpos : ∀ x ∈ G, 0 < q x) {lam : ℝ} (hlam : 0 < lam) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ G, ∀ t : ℝ, 0 < t →
      candidateDimension φ q lam t x ≤ 7 / 2 - δ := by
  obtain ⟨y, hy, hmin⟩ := hG.exists_isMinOn hne hq.continuousOn
  refine ⟨q y / lam, div_pos (hpos y hy) hlam, ?_⟩
  intro x hx t ht
  have hi : t * q y ≤ ∫ s in (0 : ℝ)..t, q (φ s x) := by
    have h := intervalIntegral.integral_mono_on ht.le
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => q y) volume 0 t)
      ((hq.comp (hφ x)).intervalIntegrable 0 t)
      (fun s _ => hmin (hinv s x hx))
    simpa using h
  have hd := (div_le_div_iff_of_pos_right (mul_pos hlam ht)).mpr hi
  have hc : t * q y / (lam * t) = q y / lam := by
    field_simp
  rw [hc] at hd
  unfold candidateDimension
  linarith

/-- Algebraic ordering and crossing index for the four proposed leading exponents.
This does not assert that any actual derivative has these exponents. -/
theorem proposed_spectrum_crossing {lam b : ℝ} (hlam : 0 < lam)
    (hb : 0 ≤ b) (hb' : b < lam / 4) :
    lam ≥ 0 ∧ 0 > -(lam / 2 + b) ∧ -(lam / 2 + b) > -lam ∧
      lam + 0 - (lam / 2 + b) > 0 ∧
      lam + 0 - (lam / 2 + b) - lam < 0 := by
  constructor
  · exact hlam.le
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem proposed_KY_branch {lam b : ℝ} (hlam : 0 < lam) :
    3 + (lam + 0 - (lam / 2 + b)) / lam = 7 / 2 - b / lam := by
  field_simp
  ring

/-- Conditional exclusion of periodic maximizers for this scalar functional.
`Periodic` is an input predicate: its identification with actual periodic
trajectories of the proposed ODE remains outside this formalization. -/
theorem no_periodic_candidate_maximizer {X : Type*} [TopologicalSpace X]
    (φ : ℝ → X → X) (q : X → ℝ) (S : Set X) (Periodic : X → Prop)
    (hφ : ∀ x, Continuous (fun s => φ s x)) (hφzero : ∀ x, φ 0 x = x)
    (hq : Continuous q) (hnonneg : ∀ x, 0 ≤ q x)
    (hzero : ∀ x, q x = 0 ↔ x ∈ S)
    (hinv : ∀ s x, x ∈ S → φ s x ∈ S)
    (hne : S.Nonempty) (haperiodic : ∀ x ∈ S, ¬ Periodic x)
    {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t) :
    ¬ ∃ p, Periodic p ∧ ∀ x,
      candidateDimension φ q lam t x ≤ candidateDimension φ q lam t p := by
  rintro ⟨p, hp, hmax⟩
  obtain ⟨x, hx⟩ := hne
  have hpx : p ∉ S := fun hs => haperiodic p hs hp
  have hlt := candidate_lt_off_zero_set φ q S hφ hφzero hq hnonneg
    hzero hlam ht hpx
  have heq := candidate_eq_on_invariant_zero_set φ q S hinv
    (fun y hy => (hzero y).mpr hy) lam t hx
  have hle := hmax x
  rw [heq] at hle
  exact (not_lt_of_ge hle) hlt

#print axioms compact_invariant_gap
#print axioms no_periodic_candidate_maximizer

end HiddenEdenPartial

/-
UNVERIFIED INFORMAL ARGUMENT — reproduced for completeness only.
Lean ignores all text in this comment. This is NOT a formal proof.

# A chaotic hidden attractor whose maximal local Lyapunov dimension is not attained on a periodic orbit

12 September 2026. Counterexample argument developed in this conversation. This is a written mathematical proof using classical existence theorems, not a published or Lean-verified result. Priority and independent verification have not been established.

## 1. Exact target and result

The second assertion in the [Kuznetsov–Eden section of Wikipedia](https://en.wikipedia.org/wiki/Eden%27s_conjecture#Kuznetsov%E2%80%93Eden%27s_conjecture) says that a hidden attractor has an embedded unstable periodic orbit attaining the maximum of its local Lyapunov dimensions.

We use the full ambient variational equation and its Euclidean singular values, as in [Kuznetsov (2016), Definitions 1–2](https://arxiv.org/pdf/1602.05410). We use the basin definition of a hidden attractor in [Kuznetsov et al. (2018), Definition 1](https://d-nb.info/1160228949/34): its basin avoids a neighborhood of each equilibrium.

**Counterexample theorem.** For some finite integer \(n\), there is a \(C^\infty\) autonomous vector field on \(\mathbb R^n\), complete for all real times and possessing a compact global attractor, with a compact hidden local attractor \(A\) such that:

- The flow on \(A\) is a transitive Anosov flow. It has a positive Lyapunov exponent, positive entropy, and dense unstable periodic orbits.
- There is a nonempty compact invariant subset \(S\subset A\) containing no periodic trajectory.
- For every \(t>0\), the Euclidean finite-time local Lyapunov dimension satisfies
  \[
  \max_{x\in A}d_L(t,x)=\frac72,
  \qquad \operatorname{argmax}_{x\in A}d_L(t,x)=S.
  \]
- Every periodic orbit \(\gamma\subset A\) has a constant \(\delta_\gamma>0\) such that
  \[
  d_L(t,x)\le\frac72-\delta_\gamma
  \quad\text{for all }x\in\gamma\text{ and all }t>0.
  \]
- Consequently the same nonattainment holds for asymptotic local dimensions and for the uniform set Lyapunov dimension, which equals \(7/2\).

The attracting set \(A\) in this construction is a smooth three-dimensional manifold with chaotic dynamics, not a set of noninteger Hausdorff dimension. Its Hausdorff dimension is 3 and its ambient Lyapunov dimension is \(7/2\). Neither equality of these dimensions nor noninteger Hausdorff dimension is a hypothesis of the hidden-attractor statement as printed.

This is a counterexample to the universal hidden assertion, not a claim that nonattainment is generic. The preceding self-excited sentence on Wikipedia contains a “typical system” qualification; its hidden sentence states no separate generic quantifier. A proposed extension of that qualifier to the hidden assertion would be a different target from the universal assertion treated here.

## 2. The chaotic base flow and an exact metric

Let

\[
B=\begin{pmatrix}2&1\\1&1\end{pmatrix},
\qquad f:\mathbb T^2\to\mathbb T^2,\quad f(x)=Bx\pmod{\mathbb Z^2}.
\]

Its eigenvalues are

\[
\Lambda=\frac{3+\sqrt5}{2}>1,\qquad \Lambda^{-1},\qquad \lambda=\log\Lambda>0.
\]

Choose unit eigenvectors \(v_u,v_s\). Form the mapping torus

\[
M=(\mathbb T^2\times\mathbb R)/\big((x,s+1)\sim(f(x),s)\big),
\]

and define the suspension flow

\[
\psi^t[x,s]=[x,s+t].
\]

The three vector fields on the covering space

\[
E_u=e^{-\lambda s}v_u,\qquad
E_s=e^{\lambda s}v_s,\qquad
E_0=\partial_s
\]

descend to smooth global vector fields on \(M\). For example, under the deck transformation \((x,s)\mapsto(f(x),s-1)\), the first vector is mapped to

\[
B(e^{-\lambda s}v_u)=e^{-\lambda(s-1)}v_u,
\]

which is the required vector at the image point. The stable vector has the corresponding transformation law.

Define a smooth Riemannian metric \(g\) on \(M\) by declaring \(E_u,E_0,E_s\) orthonormal. Then, exactly and for every \(t\),

\[
D\psi^t E_u=e^{\lambda t}E_u\circ\psi^t,
\quad D\psi^t E_0=E_0\circ\psi^t,
\quad D\psi^t E_s=e^{-\lambda t}E_s\circ\psi^t.
\tag{1}
\]

Thus the three singular values in this metric are \(e^{\lambda t},1,e^{-\lambda t}\). The metric is smooth across the suspension seam; it is not a discontinuous frame convention.

The map \(f\) is the standard hyperbolic toral automorphism. To check the dynamical properties needed here:

- Rational points of \(\mathbb T^2\) are periodic: for each denominator \(m\), \(B\) permutes the finite group \((\mathbb Z/m\mathbb Z)^2\). These points are dense. Suspension gives dense periodic orbits on \(M\).
- The Lebesgue measure is ergodic for \(f\). One elementary proof uses Fourier coefficients: invariance forces a coefficient to be constant along the orbit of its integer frequency under \(B^T\). Every nonzero such orbit is infinite, so square summability forces all nonconstant invariant coefficients to vanish. Ergodicity and full support give a dense forward orbit; its suspension is dense in \(M\).
- Equation (1) proves uniform expansion and contraction, hence the Anosov property, and gives a positive exponent \(\lambda\). The associated toral map has positive entropy. Every periodic trajectory of the suspension is unstable, since its return derivative has multiplier \(e^{\lambda T}>1\).

There are no stationary solutions of the suspension because its flow direction \(E_0\) never vanishes.

## 3. A compact invariant set with no periodic points

We need a nonempty compact \(f\)-invariant set \(K\subset\mathbb T^2\) without periodic points. Here is a construction, including the aperiodicity check.

The stable and unstable eigendirections of \(B\) have irrational slopes. Decompose a nonzero lattice vector as \(m=u+s\), with \(u\in E^u\) and \(s\in E^s\). The torus point

\[
u\bmod\mathbb Z^2=-s\bmod\mathbb Z^2
\]

is a nonzero homoclinic point of the fixed point 0: backward iterates converge to 0 using its unstable representative, and forward iterates converge using its stable representative. The intersection is transverse because the two eigendirections are distinct.

The classical Smale–Birkhoff homoclinic theorem, in its horseshoe form, therefore supplies an integer \(m_0\ge1\) and a compact set \(H\) on which \(f^{m_0}\) is conjugate to the full two-sided binary shift. This standard theorem is the only symbolic-dynamics existence result used here. The required horseshoe/full-shift form is recalled explicitly in [Araújo and Pinheiro, *Abundance of wild historic behavior*, Section 4.7.1](https://arxiv.org/pdf/1609.05356). We use this stronger form, not merely the assertion that periodic points accumulate on a transverse homoclinic point.

Fix an irrational \(\alpha\in(0,1)\). Consider the binary sequences

\[
a_n(t)=\lfloor(n+1)\alpha+t\rfloor-\lfloor n\alpha+t\rfloor,
\qquad n\in\mathbb Z,
\]

and let \(\Sigma_\alpha\) be their closure in \(\{0,1\}^{\mathbb Z}\). This set is compact, nonempty, and invariant under the shift and its inverse, since shifting replaces \(t\) by \(t+\alpha\).

Every block of length \(N\) in a sequence in \(\Sigma_\alpha\) has a number of 1s differing from \(N\alpha\) by at most 1. This follows by telescoping the floor differences and then taking limits in the sequence space. Consequently every sequence has limiting frequency \(\alpha\) of the symbol 1. A periodic binary sequence has rational frequency, so \(\Sigma_\alpha\) contains no periodic sequence.

Let \(K_0\subset H\) be the image of \(\Sigma_\alpha\) under the conjugacy, and set

\[
K=\bigcup_{j=0}^{m_0-1} f^j(K_0).
\]

This is compact, nonempty, and \(f\)-invariant. If it contained an \(f\)-periodic point, a corresponding point in \(K_0\) would be periodic for \(f^{m_0}\), contradicting the construction of \(\Sigma_\alpha\).

Let \(S_M\subset M\) be the suspension of \(K\). This is a nonempty compact invariant subset with no periodic trajectory. Indeed, any period of the suspension must be an integer because the clock coordinate advances at unit speed; it would then give an \(f\)-periodic point in \(K\).

## 4. A smooth nonnegative function detecting the aperiodic set

There is a smooth function

\[
q:M\to[0,\lambda/4),\qquad q^{-1}(0)=S_M.
\tag{2}
\]

For completeness, any closed subset of a smooth compact manifold can be realized this way. Cover its complement by countably many relatively compact coordinate balls and choose nonnegative smooth bump functions \(b_j\) supported in those balls, whose positive sets cover the complement. Choose positive weights \(c_j\) so small that

\[
\|c_j b_j\|_{C^j}\le2^{-j}.
\]

The series \(F=\sum_j c_jb_j\) converges with all derivatives, vanishes on the closed set, and is positive at every point of its complement. Then

\[
q=\frac{\lambda}{4}\frac{F}{1+F}
\]

has the stated properties. In particular, no analyticity of \(q\) is claimed.

For every periodic orbit \(\gamma\) of \(\psi\), compactness and disjointness from \(S_M\) imply

\[
q_\gamma:=\min_{x\in\gamma}q(x)>0.
\tag{3}
\]

The constants in (3) can depend on the orbit. No positive gap uniform over all periodic orbits is asserted.

## 5. Euclidean realization with the required variational equation

Use the smooth Nash embedding theorem to choose a smooth **isometric** embedding

\[
\iota:(M,g)\hookrightarrow\mathbb R^N
\]

for some finite \(N\). An accessible proof of the exact smooth theorem used here is [Petrunin, *Nash's theorem via Günther's trick*, Theorem 1.1](https://anton-petrunin.github.io/530/tex/the-nash.pdf). The theorem is used as a classical existence theorem, not claimed to have been re-proved or computationally implemented here.

Work in \(\mathbb R^{N+1}=\mathbb R^N\times\mathbb R\). A tubular neighborhood of \(\iota(M)\times\{0\}\) can be described by

\[
\Theta(x,v,z)=(\iota(x)+v,z),
\qquad v\in\nu_x\iota(M),\quad z\in\mathbb R,
\]

where \(\nu\iota(M)\) is the Euclidean normal bundle. Set

\[
L=2\lambda,\qquad a=\lambda/2.
\]

Let \(\nabla\) be the metric normal connection obtained by orthogonal projection of the Euclidean connection. In a small tubular neighborhood define the smooth system by

\[
\boxed{
\dot x=E_0(x),\qquad
\nabla_t v=-Lv,\qquad
\dot z=-(a+q(x))z.}
\tag{4}
\]

The covariant equation specifies a usual smooth vector field on the normal bundle. Pushing it forward through \(\Theta\) gives an ordinary smooth autonomous vector field on an open subset of Euclidean space.

Let \(P_x^t\) be normal parallel transport along \(\psi^t x\). Since the connection is metric, \(P_x^t\) is an isometry between the normal fibers. In these coordinates the forward flow of (4) is

\[
\left(\psi^t x,\ e^{-Lt}P_x^t v,\
z\exp\left[-at-\int_0^t q(\psi^s x)\,ds\right]\right).
\tag{5}
\]

The zero section

\[
A=\{\Theta(x,0,0):x\in M\}
\]

is a compact local attractor. In fact the normal distance contracts at least as fast as \(e^{-at}\), so a sufficiently small closed tubular neighborhood is a trapping neighborhood with maximal invariant set exactly \(A\). The flow on \(A\) is the transitive suspension flow already constructed. This also makes \(A\) a minimal local attractor, rather than an arbitrary union of invariant components: a proper closed attracting subset would have a relatively open basin meeting \(A\), incompatible with the dense forward orbit in \(A\).

**Why the singular values really are Euclidean.** At the zero section, the derivative of \(\Theta\) identifies tangent vectors via \(D\iota\), normal vectors via their actual Euclidean vectors, and the last coordinate with an orthogonal Euclidean line. These identifications are isometric and mutually orthogonal. Differentiating (5) at \(v=z=0\) gives a block diagonal map: the derivatives of parallel transport and of \(q\) with respect to the base are multiplied by \(v\) or \(z\), so produce no off-diagonal block there.

Together with (1), this proves that the singular values of the full Euclidean derivative along \(A\) are exactly

\[
\boxed{
e^{\lambda t},\quad1,\quad e^{-at-Q_t(x)},\quad e^{-\lambda t},\quad
\underbrace{e^{-Lt},\ldots,e^{-Lt}}_{N-3},
\qquad Q_t(x)=\int_0^t q(\psi^s x)\,ds.}
\tag{6}
\]

These are already in decreasing order, because

\[
\lambda/2\le a+Q_t(x)/t<3\lambda/4<\lambda<L.
\]

Thus the construction does not replace the Euclidean definition with a conveniently chosen norm. The chosen metric is realized by an actual isometric Euclidean embedding, and (6) concerns the derivative of the resulting Euclidean ODE.

## 6. Make the attractor hidden and the system global

We now modify the system only away from a smaller tube around \(A\). Let

\[
\rho^2=\|v\|^2+z^2,
\]

and choose \(0<r_0<R\) small enough that \(\rho\le R\), and a slightly larger neighborhood, lie in the tubular coordinate domain. Choose a smooth scalar function \(h\) with

\[
h(s)=0\quad(0\le s\le r_0^2),\qquad h(R^2)=3L.
\]

In the larger tube, replace (4) by

\[
\dot x=E_0(x),\qquad
\nabla_t v=(-L+h(\rho^2))v,\qquad
\dot z=(-a-q(x)+h(\rho^2))z.
\tag{7}
\]

There are no equilibria in this entire tube: its projection onto \(M\) always has nonzero component \(E_0\). The vector field agrees with (4) on \(\rho\le r_0\), so the attractor and every derivative calculation along it are unchanged.

For the compact outer tube \(D=\Theta\{\rho\le R\}\), its boundary satisfies

\[
\frac{d}{dt}\rho^2
=2(3L-L)\|v\|^2+2(3L-a-q(x))z^2>0.
\tag{8}
\]

Thus the field points strictly outward through \(\partial D\). The exterior of \(D\) is forward invariant: an inward crossing would contradict (8).

Extend the vector field smoothly to all of \(\mathbb R^{N+1}\), agreeing with (7) on a neighborhood of \(D\) and agreeing with \(-w\) outside a large ball, where \(w\) denotes the ambient coordinate. This is done by a smooth cutoff supported in the tubular coordinate neighborhood. The field has bounded derivative and at most linear growth, so its flow is complete for both signs of time. Since it is \(-w\) outside a compact set, a sufficiently large ball is a bounded-set absorbing set, giving a compact global attractor.

Additional equilibria of the extension lie outside \(D\). By (8), their neighborhoods outside \(D\) cannot send trajectories into \(D\), whereas a trajectory approaching \(A\subset\operatorname{int}D\) must eventually lie in \(D\). Hence

\[
B(A)\subset\operatorname{int}D,
\qquad D\cap\operatorname{Eq}(X)=\varnothing.
\tag{9}
\]

Every equilibrium therefore has an open neighborhood disjoint from \(B(A)\), proving that \(A\) is hidden in the published basin sense. In fact the compact set \(D\) has positive distance from the closed equilibrium set, so one can choose a neighborhood of the entire equilibrium set disjoint from \(B(A)\).

This need not be a vacuous no-equilibrium example. Translate the embedding and choose the cutoff so its support avoids the origin. The extension then equals \(-w\) near the origin and has a hyperbolic stable equilibrium there, still separated from \(B(A)\).

## 7. Exact dimension and exclusion of every periodic orbit

For a time \(t>0\), let the finite-time exponents be \(t^{-1}\log\sigma_i(D\Phi^t)\), ordered decreasingly, and use the usual Kaplan–Yorke interpolation. Formula (6) gives

\[
\lambda,\quad0,\quad-a-\frac{Q_t(x)}t,\quad-\lambda,\quad-L,\ldots,-L.
\tag{10}
\]

The sum of the first three is strictly positive, and the sum of the first four is strictly negative. Thus the Kaplan–Yorke index is always 3, and

\[
\boxed{
d_L(t,\Theta(x,0,0))
=3+\frac{\lambda-a-Q_t(x)/t}{\lambda}
=\frac72-\frac{1}{\lambda t}\int_0^t q(\psi^s x)\,ds.}
\tag{11}
\]

Identify \(S=\Theta(S_M,0,0)\). If \(x\in S_M\), invariance and (2) give \(Q_t(x)=0\) for every \(t>0\). If \(x\notin S_M\), then \(q(x)>0\), and continuity gives \(Q_t(x)>0\) for every \(t>0\). Consequently

\[
\max_{u\in A}d_L(t,u)=\frac72,
\qquad \operatorname{argmax}_{u\in A}d_L(t,u)=S,
\quad t>0.
\tag{12}
\]

An equivalent exact volume calculation is

\[
\omega_{7/2}(D\Phi^t(\Theta(x,0,0)))=e^{-Q_t(x)}\le1.
\]

For \(0<\varepsilon<1/2\),

\[
\omega_{7/2+\varepsilon}(D\Phi^t(\Theta(x,0,0)))
=e^{-\varepsilon\lambda t-Q_t(x)}<1.
\]

These identities also verify the set-dimension threshold directly, without any exchange of limits and suprema.

Every periodic orbit \(\gamma\subset A\) corresponds to a periodic orbit of the suspension and is unstable. It is disjoint from \(S\), and (3) and (11) give

\[
\boxed{d_L(t,u)\le\frac72-\frac{q_\gamma}{\lambda}<\frac72
\quad(u\in\gamma,\ t>0).}
\tag{13}
\]

Thus not one embedded unstable periodic orbit can attain the maximum.

For its asymptotic value, if \(T_\gamma\) is a period, set

\[
\overline q_\gamma=\frac1{T_\gamma}\int_0^{T_\gamma}q(\psi^s x)\,ds>0.
\]

The periodic Floquet exponents and local dimension are

\[
\lambda,\ 0,\ -\lambda/2-\overline q_\gamma,\ -\lambda,\ -L,\ldots,-L,
\qquad
d_L(\gamma)=\frac72-\frac{\overline q_\gamma}{\lambda}<\frac72.
\tag{14}
\]

At every point of \(S\), all the exponents have limits and the local dimension is \(7/2\). For other points the average of \(q\) need not converge; nevertheless (11) bounds every finite-time value, and hence every limsup or liminf version, by \(7/2\). No claim of existence of all individual Lyapunov limits at every point is needed.

Finally, for the uniform set definition,

\[
\boxed{D_L(A)=\inf_{t>0}\sup_{u\in A}d_L(t,u)=\frac72.}
\tag{15}
\]

Equations (12)–(15) establish the claimed failure for both finite-time and standard asymptotic interpretations. Dense periodic orbits do not force a maximum to be attained on a periodic orbit: the set of periodic points is not closed. In fact for fixed \(t\), continuity of (11) and density of periodic points imply that their supremum is also \(7/2\), but no periodic point attains it.

## 8. What this does and does not establish

The proof addresses the hidden-attractor assertion with the full Euclidean variational equation. Its invariant set is a genuine transitive hyperbolic local attractor, is hidden by the actual equilibrium-basin definition, and has dense unstable periodic orbits. The nonperiodic maximizers are explicitly separated from every periodic orbit by (13), with no numerical orbit enumeration.

It is important not to substitute a different dimension: restricting the derivative to the tangent bundle of the attracting three-manifold would discard the weak normal exponent and give a different quantity. The source definition takes the derivative of the full ambient ODE; that is what (6)–(15) calculate.

The construction does not prove the following additional claims:

- that periodic nonattainment holds on an open or residual set of vector fields;
- that the example is polynomial, analytic, three-dimensional, or given by an explicit coefficient list;
- that the attractor has noninteger Hausdorff dimension;
- that Eden's different original/global-attractor conjecture is resolved by this local example;
- that the construction has not appeared previously, or that the paper is publication-ready.

The distinction between universal attainment and generic attainment is substantive. For context, [Anikushin, Remark 3.9](https://arxiv.org/pdf/2304.05713) discusses the connection with generic maximizing-measure questions in ergodic optimization. This note does not refute those generic conjectures. It refutes the unqualified hidden-attractor assertion printed on the requested Wikipedia page.

The argument rests on two substantial classical existence theorems, explicitly identified above: Smale–Birkhoff and the smooth Nash embedding theorem. The remaining construction, the hidden-basin separation, and the exact Euclidean singular-value calculation are supplied here. No independent referee check or full Lean formalization has been completed.

-/
