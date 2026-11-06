import Mathlib

open Finset

/- If $f\left( x \right)=x+3$, ${{f}_{1}}\left( x \right)=f\left( x \right)$, ${{f}_{2}}\left( x \right)=f\left( {{f}_{1}}\left( x \right) \right)$, ${{f}_{3}}\left( x \right)=f\left( {{f}_{2}}\left( x \right) \right)$, $\cdots \cdots $, ${{f}_{k+1}}\left( x \right)=f\left( {{f}_{k}}\left( x \right) \right)$, then ${{f}_{1}}\left( 1 \right)+{{f}_{2}}\left( 2 \right)+{{f}_{3}}\left(3 \right)+\cdots +{{f}_{100}}\left( 100 \right)=$ ___          ___. -/
theorem algebra_7422 {f : ℕ → ℕ → ℕ} (hf : ∀ x, f 0 x = x + 3)
    (hfn : ∀ n, f (n + 1) = f 0 ∘ f n) :
    ∑ i ∈ range 100, f i (i + 1) = 20200 := by
  have h1 : ∀ n, f n = fun x => x + 3 * (n + 1) := by
    intro n
    induction n with
    | zero =>
      funext x
      simp [hf]
    | succ n ih =>
      rw [hfn n]
      rw [ih]
      funext y
      simp [hf]
      <;> ring
  have eq1 : ∀ (i : ℕ), f i (i + 1) = 4 * (i + 1) := by
    intro i
    have eq2 : f i = fun x => x + 3 * (i + 1) := h1 i
    rw [eq2]
    simp [mul_add, add_mul]
    <;> ring
  have h2 : ∑ i ∈ range 100, f i (i + 1) = ∑ i ∈ range 100, 4 * (i + 1) := by
    apply Finset.sum_congr
    · rfl
    · intro i hi
      have eq3 : f i (i + 1) = 4 * (i + 1) := eq1 i
      simpa using eq3
  rw [h2]
  norm_num [Finset.sum_range_succ]