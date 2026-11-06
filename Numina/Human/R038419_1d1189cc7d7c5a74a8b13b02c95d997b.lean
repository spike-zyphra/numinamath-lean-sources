import Mathlib

/-
  Given that the two zeros of the function $f(x)=x^{2}+ax+b$
  are $-2$ and $3$, find the solution set of the inequality $af(-2x) > 0$.
-/
theorem algebra_9424 {a b : ℝ} (f : ℝ → ℝ) (hf : f = fun x => x ^ 2 + a * x + b)
    (hzeros : f (-2) = 0 ∧ f 3 = 0) :
    {x | a * f (- 2 * x) > 0} = {x | -3 / 2 < x ∧ x < 1} := by

  -- solve inequality x^2+bx+c<0
  have root (b c x : ℝ) : x ^ 2 + b * x + c < 0 →
      x > (-b - √(b ^ 2 - 4 * c)) / 2 ∧ x < (-b + √(b ^ 2 - 4 * c)) / 2 := by
    intro hx
    have : (2 * x + b) ^ 2 < b ^ 2 - 4 * c := by linarith
    have h1 : 2 * x + b < √ (b ^ 2 - 4 * c) := by exact Real.lt_sqrt_of_sq_lt this
    have h2 : 2 * x + b > - √ (b ^ 2 - 4 * c) := by exact Real.neg_sqrt_lt_of_sq_lt this
    constructor <;> linarith

  have root' (x1 x2 x : ℝ) (hx2 : x1 < x ∧ x < x2) : x ^ 2 - (x1 + x2) * x + x1 * x2 < 0 := by
    have h : (x - x1) * (x - x2) < 0 := by
      refine mul_neg_of_pos_of_neg ?ha ?hb
      · linarith [hx2.left]
      · linarith [hx2.right]
    linarith

  -- solve hzeros
  -- a = -1
  -- b = -6
  obtain ⟨h1, h2⟩ := hzeros
  simp [hf] at h1 h2
  have ha : a = -1 := by linarith
  have hb : b = -6 := by linarith
  -- simplify af(-2x)>0
  simp [ha, hb, hf]
  apply Set.ext
  intro x
  constructor <;> intro hx
  · simp at hx
    norm_cast at hx
    -- solve the inequality
    have after_simp : x ^ 2 + (1 / 2) * x - 3 / 2 < 0 := by linarith
    apply root _ _ x at after_simp
    have : √((1 / 2) ^ 2 - 4 * - (3 / 2)) = 5 / 2 := by
      refine (Real.sqrt_eq_iff_mul_self_eq_of_pos ?_).mpr ?_
      all_goals linarith
    rw [this] at after_simp
    obtain ⟨h1, h2⟩ := after_simp
    norm_num at h1 h2
    constructor <;> linarith
  · -- verify the answer
    simp at hx
    obtain ⟨h1, h2⟩ := hx
    have h := root' (-3/2) 1 x  ?_
    simp
    split_ands
    all_goals linarith
