import Mathlib

/- functional equation : f(a(x+y)) = f(x) + f(y) -/
def feq (f : ℝ → ℝ) (a : ℝ) := ∀ x y, f (a * (x + y)) = f x + f y

/- For which values of \(\alpha\) does there exist a non-constant function \(f: \mathbb{R} \rightarrow \mathbb{R}\) such that:
\[ f(\alpha(x+y)) = f(x) + f(y) ? \]-/
theorem functional_equations_4190 (a : ℝ) : a ≠ 1 ↔ ∀ f, feq f a → ∃ c, ∀ x, f x = c := by
  constructor
  . intro ha f hf
    -- if a≠1 then f(x)=0 forall real number x
    use 0
    intro x
    -- need ne_zero condition to perform field_simp
    have : a - 1 ≠ 0 := sub_ne_zero_of_ne ha
    let y := -a * x / (a - 1)
    have hy : y = a * (x + y) := by field_simp [y]; ring
    -- assign y=-ax/(a-1) to f(a(x+y)) = f(x) + f(y)
    specialize hf x y
    -- use `y=a(x+y)` to deduce `f(y)=f(x)+f(y)`
    rw [← hy] at hf
    -- cancel `f(y)`, we have `f(x)=0`
    linear_combination -hf
  -- prove a≠1 by contradiction
  intro h ha
  -- f(x)=x is a counterexample
  let f : ℝ → ℝ := fun x => x
  -- f(x)=x satisfies f(x+y)=f(x)+f(y), but it is not constant function
  have hf : feq f a := by simp [feq, ha]
  obtain ⟨c, hc⟩ := h f hf
  have : f 0 = f 1 := by rw [hc 0, eq_comm]; exact hc 1
  norm_num at this
