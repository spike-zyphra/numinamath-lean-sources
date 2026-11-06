import Mathlib

/- A real-valued function f has the property that for all real numbers a and b,
f(a+b) + f(a-b) = 2 f(a) f(b)
Which one of the following cannot be the value of f(1)?
(A) 0
(B) 1
(C) −1
(D) 2
(E) − 2
-/

theorem algebra_95919 {f : ℝ → ℝ} (h : ∀ a b, f (a + b) + f (a - b) = 2 * f a * f b) : f 1 ≠ -2 := by
  -- plug in a = b to get ha: f(2a) + f(0) = 2*f(a)^2
  have ha: ∀ a: ℝ, f (2 * a) + f 0 = 2 * (f a)^2 := by
    intro a
    calc
      f (2 * a) + f 0 = f (a + a) + f (a - a) := by ring_nf
      _ = 2 * f a * f a := by rw [h a a]
      _ = 2 * (f a)^2 := by ring
  -- plug in a = 0 in ha to get hz: f(0) * (1-f(0)) = 0
  have hz: f 0 * (1 - (f 0)) = 0 := by
    calc
      f 0 * (1 - (f 0)) = (f (2*0) + f 0 - 2 * (f 0)^2) / 2 := by ring_nf
      _ = (2 * (f 0)^2 - 2 * (f 0)^2) / 2 := by rw [ha]
      _ = 0 := by ring
  -- hz implies f(0) = 0 or f(0) = 1, which means 0 ≤ f(0) ≤ 1
  have hz' : f 0 = 0 ∨ 1 - f 0 = 0 := by exact mul_eq_zero.mp hz
  have hz_ub : f 0 ≤ 1 := by
    cases hz' with
    | inl hzv => simp [hzv]
    | inr hzv => rw [sub_eq_zero.mp hzv]
  -- now h_lb: f(2a) = 2 * f(a)^2 - f(0) > 0 - 1
  have h_lb : ∀ a: ℝ, -1 ≤ f (2 * a) := by
    intro a
    calc
      -1 ≤ 0 - 1 := by norm_num
      _ ≤ 2 * (f a)^2 - f 0 := by
        apply tsub_le_tsub
        . apply Left.mul_nonneg
          . norm_num
          . exact sq_nonneg (f a)
        . exact hz_ub
      _ = f (2 * a) := by
        rw [← ha a]
        ring
  -- so pluggin in a = 1/2 in h_lb gives -1 ≤ f(1)
  have h1_lb : -1 ≤ f 1 := by
    calc
      -1 ≤ f (2 * (1/2)) := by exact h_lb (1/2)
      _ = f 1 := by norm_num
  -- now f(1) = -2 is contradiction with -1 ≤ f(1)
  intro hf
  rw [hf] at h1_lb
  norm_num at h1_lb