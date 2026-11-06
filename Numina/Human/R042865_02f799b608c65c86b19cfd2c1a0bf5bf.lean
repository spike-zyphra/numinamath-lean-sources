import Mathlib

/- Find all functions $f: \mathbb{R} \rightarrow \mathbb{R}$ such that

$$
f(f(x) f(1-x))=f(x) \quad \text { and } \quad f(f(x))=1-f(x)
$$

for all real $x$. -/
theorem algebra_608040 :
  { f : ℝ → ℝ | ∀ x : ℝ, f (f x * f (1 - x)) = f x ∧ f (f x) = 1 - f x } = {fun _ ↦ 1 / 2} := by
  ext f
  simp
  constructor
  -- We first show that f(x) = 1 / 2 is a solution.
  swap
  . rintro rfl
    simp
    norm_num
  -- We now show that any solution must be f(x) = 1 / 2.
  . intro h
    -- Split the two equations.
    have h₁ x := (h x).1
    have h₂ x := (h x).2
    clear h
    -- We have the following equation 3:
    -- f(f(f(x))) =(2) 1 - f(f(x)) =(2) f(x)
    have h₃ x : f (f (f x)) = f x := by
      calc
        _ = 1 - f (f x) := by rw [h₂]
        _ = f x := by simp [h₂]
    -- We have the following equation 4:
    -- f(f(x)) =(1) f(f(x) f(1-x)) =(2) f(f(f(x)) f(f(f(x)))) =(3) f(f(f(x)) f(x))
    have h₄ x : f (f x) = f (f (f x) * f x) := by
      calc
        _ = f (f (f x) * f (1 - f x)) := by rw [h₁]
        _ = f (f (f x) * f (f (f x))) := by rw [← h₂]
        _ = f (f (f x) * f x) := by rw [h₃]
    -- We have the following equation 5:
    -- f(x) =(3) f(f(f(x))) =(4) f(f(f(x)) f(f(f(x)))) =(3) f(f(x) f(f(x))) =(mul_comm) f(f(f(x)) f(x)) =(4) f(f(x)) =(2) 1 - f(x)
    have h₅ x : f x = 1 - f x := by
      calc
        _ = f (f (f x)) := by rw [h₃]
        _ = f (f (f (f x)) * f (f x)) := by rw [← h₄]
        _ = f (f x * f (f x)) := by rw [h₃]
        _ = f (f (f x) * f x) := by rw [mul_comm]
        _ = f (f x) := by rw [← h₄]
        _ = 1 - f x := by rw [h₂]
    -- So we get that f(x) = 1 / 2 for all x.
    ext x
    linarith only [h₅ x]
