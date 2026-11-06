import Mathlib

open Set Polynomial

/- if `0<x<1`, then `0<x^2<1` -/
lemma aux1 {x : ℝ} (h : x ∈ Ioo 0 1) : x * x ∈ Ioo 0 1 := by
  constructor <;> nlinarith [h.1, h.2]

/- if `0<x<1`, then `0<x^3<1` -/
lemma aux2 {x : ℝ} (h : x ∈ Ioo 0 1) : x * x * x ∈ Ioo 0 1 := by
  have := aux1 h
  constructor <;> nlinarith [this.1, this.2, h.1, h.2]

/- Determine the functions \( f:(0,1) \rightarrow \mathbf{R} \) for which:
\[ f(x \cdot y) = x \cdot f(x) + y \cdot f(y) \]-/
theorem functional_equations_4191 {f : ℝ → ℝ} (h : ∀ x ∈ Ioo 0 1, ∀ y ∈ Ioo 0 1, f (x * y) = x * f x + y * f y) :
    ∀ x ∈ Ioo 0 1, f x = 0 := by
  -- **Substitute \( y = x \) into the equation:**
  --  \[
  --  f(x^2) = x \cdot f(x) + x \cdot f(x) = 2x \cdot f(x)
  --  \]
  have h1 {x} (hx : x ∈ Ioo 0 1) := h x hx x hx
  -- **Consider \( y = x^2 \) for the next step:**
  --  \[
  --  f(x^3) = f(x \cdot x^2) = x \cdot f(x) + x^2 \cdot f(x^2)
  --  \]
  --  From the previous result, substitute \( f(x^2) = 2x \cdot f(x) \):
  --  \[
  --  f(x^3) = x \cdot f(x) + x^2 \cdot (2x \cdot f(x)) = x \cdot f(x) + 2x^3 \cdot f(x) = (x + 2x^3) \cdot f(x)
  --  \]
  have h2 {x} (hx : x ∈ Ioo 0 1) := h x hx (x * x) (aux1 hx)
  -- **Substitute \( y = x^3 \) into the given equation:**
  --  \[
  --  f(x^4) = f(x \cdot x^3) = x \cdot f(x) + x^3 \cdot f(x^3)
  --  \]
  --  Using \( f(x^3) = (x + 2x^3) \cdot f(x) \):
  --  \[
  --  f(x^4) = x \cdot f(x) + x^3 \cdot (x + 2x^3) \cdot f(x) = x \cdot f(x) + x^4 \cdot f(x) + 2x^6 \cdot f(x) = (x + x^4 + 2x^6) \cdot f(x)
  --  \]
  have h3 {x} (hx : x ∈ Ioo 0 1) := h x hx (x * x * x) (aux2 hx)
  -- **Alternatively calculate \( f(x^4) \) by substituting \( y = x^2 \):**
  --  \[
  --  f(x^4) = f(x^2 \cdot x^2) = 2x^2 \cdot f(x^2)
  --  \]
  --  Using \( f(x^2) = 2x \cdot f(x) \):
  --  \[
  --  f(x^4) = 2x^2 \cdot (2x \cdot f(x)) = 4x^3 \cdot f(x)
  --  \]
  have h3' {x} (hx : x ∈ Ioo 0 1) := h (x * x) (aux1 hx) (x * x) (aux1 hx)
  -- **Equating the two expressions for \( f(x^4) \):**
  --  \[
  --  4x^3 \cdot f(x) = (x + x^4 + 2x^6) \cdot f(x)
  --  \]
  have H {x} (hx : x ∈ Ioo 0 1) : x ^ 3 * 4 * f x = (x + x ^ 4 + x ^ 6 * 2) * f x := by
    specialize h1 hx
    specialize h2 hx; rw [h1] at h2
    specialize h3 hx; rw [← mul_assoc] at h2; rw [h2] at h3
    specialize h3' hx; rw [h1] at h3'
    rw [show x*x*(x*x)=x*x*x*x by ring] at h3'
    rw [show x*(x*x*x)=x*x*x*x by ring, h3'] at h3
    linarith
  by_contra H'
  push_neg at H'
  rcases H' with ⟨x0, ⟨hx0, hfx0⟩⟩
  have nezero_of_nezero {x} (hx : x ∈ Ioo 0 1) (hf : f x ≠ 0) : f (x * x) ≠ 0 := by
    rw [h1 hx, ← add_mul]
    refine mul_ne_zero ?_ hf
    linarith [hx.1]
  have zero_of_nezero {x} (hx : x ∈ Ioo 0 1) (hf : f x ≠ 0) :
      2 * x ^ 6 + x ^ 4 - 4 * x ^ 3 + x = 0 := by
    specialize H hx
    rw [mul_left_inj' hf] at H
    linear_combination -H
  let S : Set ℝ := {x ∈ Ioo 0 1 | 2 * x ^ 6 + x ^ 4 - 4 * x ^ 3 + x = 0}
  let P : ℝ[X] := C 2 * X ^ 6 + X ^ 4 - C 4 * X ^ 3 + X
  -- **Analyze the derived identity:**
  --  \[
  --  4x^3 = x + x^4 + 2x^6
  --  \]
  --  This equality must hold for all \( x \in (0, 1) \). Consider two cases:
  --  - \( f(x) = 0 \)
  --  - Solve for non-trivial solutions of \( 4x^3 = x + x^4 + 2x^6 \), which can only have at most 6 solutions in the interval \( (0, 1) \) due to the polynomial being of degree 6. This implies that except for at most 6 points, \( f(x) = 0 \).
  have : S.Finite := by
    have : S ⊆ P.rootSet ℝ := by
      intro x hx
      rw [mem_rootSet]
      simp [P]
      constructor
      . intro h
        apply_fun fun p => p.coeff 1 at h
        simp at h
      exact hx.2
    refine Finite.subset ?_ this
    apply rootSet_finite
  let F : ℕ ↪ ℝ := {
    toFun := fun n => x0 ^ 2 ^ n
    inj' := by
      intro n m h
      simp at h
      replace h := pow_right_injective hx0.1 (ne_of_lt hx0.2) h
      apply Nat.pow_right_injective <| le_refl _
      exact h
  }
  -- **Attempt a contradiction to check for non-zero solutions:**
  --  Suppose \( f(x) \neq 0 \) for some \( x \in (0, 1) \). Then \( f(x^2) = 2x \cdot f(x) \neq 0 \), and similarly \( f(x^4) \neq 0 \), and so on.
  --  This process generates an infinite sequence \( x_n = x^{2^n} \) in \( (0, 1) \), for which \( f(x_n) \neq 0 \).
  have hF n : (F n ∈ Ioo 0 1) ∧ f (F n) ≠ 0 ∧ F n ∈ S := by
    induction' n with n ih
    . rw [show F 0 = x0 ^ 2 ^ 0 from rfl, pow_zero, pow_one]
      exact ⟨hx0, hfx0, ⟨hx0, zero_of_nezero hx0 hfx0⟩⟩
    rw [show F (n + 1) = F n ^ 2 by simp [F]; ring, pow_two]
    have Hx0 := aux1 ih.1
    have Hfx0 : f (F n * F n) ≠ 0 := nezero_of_nezero ih.1 ih.2.1
    exact ⟨Hx0, Hfx0, ⟨Hx0, zero_of_nezero Hx0 Hfx0⟩⟩
  have : S.Infinite := infinite_of_injective_forall_mem F.inj' (fun n => (hF n).2.2)
  -- **Conclusion by contradiction:**
  --  There can only be at most 6 points where \( f(x) \neq 0 \), but we constructed an infinite sequence. Therefore, \( f(x) \neq 0 \) at any \( x \in (0, 1) \) cannot hold.
  contradiction
