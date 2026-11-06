import Mathlib

/- Let P(x) be a quadratic polynomial with real coefficients satisfying x^2-2x+2 <= P(x) <= 2x^2-rx+3 for all real numbers x, and suppose P(11) = 181. Find P(16).
-/
theorem algebra_94528 {P : ℝ → ℝ} (a b c : ℝ) (hP : P = fun x => a*x^2 + b*x + c) (ha: a ≠ 0) (hP' : ∀ x, x^2 - 2*x + 2 ≤ P x ∧ P x ≤ 2*x^2 - 4*x + 3) (hP'' : P 11 = 181) : P 16 = 406 := by
  -- first establish that ax^2+bx+c = (x+b/(2a))^2 + c - b^2/(4a)
  set L := (c - b^2 / (4 * a)) with hL
  have hP_sq : P = fun x => a * (x + b / (2*a))^2 + L := by
    rw [hP]
    ext x
    calc
      a * x ^ 2 + b * x + c = a * x^2 + 2 * a * b/(2 * a) * x + a * b^2/(4 * a^2) + c - b^2/(4 * a) := by
        have h₁ : 2 * a * b/ (2 * a) * x = b * x := by field_simp
        have h₂ : a * b^2/(4 * a^2) = b^2 / (4 * a) := by field_simp; ring
        rw [h₁, h₂]
        ring
      _ = a * (x + b / (2*a))^2 + L := by ring
  -- next establish that P(-b/(2a)) = L
  have hL_val : P (-b/(2*a)) = L := by
        simp [hP_sq]
        right
        field_simp
  -- due to x^2 - 2x - 2 = (x-1)^2 + 1, it holds that 1 ≤ P(x) for all x
  have hP_lb' : ∀ x:ℝ, 1 ≤ P x := by
    intro x
    calc
    1 ≤ (x-1)^2 + 1 := by simp [sq_nonneg]
    _ = x^2 - 2*x + 2 := by ring
    _ ≤ P x := by exact (hP' x).left
  -- prove that 0 ≤ a, in particular 0 < a
  have ha_nonneg : 0 ≤ a := by
    -- 1 ≤ L and in parituclar 0 ≤ L
    have hL' : 1 ≤ L := by
      rw [← hL_val]
      exact hP_lb' (-b/(2*a))
    have hL' : 0 ≤ L := by linarith
    -- assume a < 0 to prove contradiction
    by_contra ha_neg
    -- plug in x = √(L/|a|) - b/(2*a), to prove that means 1 ≤ -L + L = 0, contradiction
    have ha_neg : a < 0 := by linarith
    have ha_ratio : a / |a| = - 1:= by
      rw [abs_of_neg ha_neg]
      field_simp
    have ha_abs_pos : 0 < |a| := by exact abs_pos.mpr ha
    have : 0 ≤ L / |a| := by
      calc
        0 ≤ 0 / |a| := by field_simp
        _ ≤ L / |a| := by exact (div_le_div_iff_of_pos_right ha_abs_pos).mpr hL'
    have : (1:ℝ) ≤ 0 := by
      calc
        1 ≤ P (√(L/|a|) - b/(2*a)) := by exact hP_lb' _
        _ ≤ a * (√(L/|a|) - b/(2*a) + b/(2*a))^2 + L := by simp [hP_sq]
        _ = a * (√(L/|a|))^2 + L := by ring
        _ = a * (L / |a|) + L := by
          congr
          simp only [Real.sq_sqrt, this]
        _ = (a / |a|) * L + L := by ring
        _ = -1 * L + L := by rw [ha_ratio]
        _ = 0 := by ring
    linarith
  have ha_pos : 0 < a := by
    have : 0 < a ∨ a = 0 := by exact LE.le.gt_or_eq ha_nonneg
    exact Or.resolve_right this ha
  -- for all x L ≤ P(x) as P(x) = some square + L
  have hP_lb : ∀ x:ℝ, L ≤ P x := by
    intro x
    have : 0 ≤ a * (x + (b / (2*a)))^2 := by simp [sq_nonneg, ha_pos]
    calc
      L ≤ a * (x + (b / (2*a)))^2 + L := by simp [this]
      _ = P x := by simp [hP_sq]
  -- 1 ≤ P(1) ≤ 1 by plugging in, so P(1) = 1
  have hP1_lb : 1 ≤ P 1 := by
    have := (hP' 1).left; simp at this; assumption
  have hP1_ub : P 1 ≤ 1 := by
    have := (hP' 1).right; simp at this; norm_num at this; assumption
  have hP1 : P 1 = 1 := by linarith
  -- so L ≤ P(1) = 1 and and 1 ≤ P(-b/(2a)) = L, so L = 1
  have hL_eq_1 : L = 1 := by
    apply le_antisymm
    . rw [← hP1]
      exact hP_lb 1
    . rw [← hL_val]
      exact hP_lb' (-b/(2*a))
  -- pluggin in L = 1 at P(1)'s definition gives b = -2a
  have h_ab : b = -2 * a := by
    simp [hP_sq] at hP1
    rw [hL_eq_1] at hP1
    have : a * (1 + b / (2*a))^2 = 0 := by linarith
    simp [ha] at this
    field_simp at this
    linarith
  -- P(1) = 1 means a+b+c=1
  have habc₁ : a + b + c = 1 := by
    simp [hP] at hP1; assumption
  -- P(11) = 1 means 121a+11b+c = 181
  have habc₂ : 121 * a + 11 * b + c = 181 := by
    simp [hP] at hP''; linarith
  -- due to b = -2a i.e. 1 being minimal point, 11 and -9 have symmetric value (proved by using b = -2a to get (11 + b/(2a))^2 = (-9 + b/(2a))^2. so P(-9) = 181 also and 81a-9b+c = 181
  have habc₃ : P (-9) = 181 := by
    calc
      P (-9) = a * (-9 + b / (2*a))^2 + L := by simp [hP_sq]
      _ = a * (-9 - 1)^2 + L := by
        congr
        rw [h_ab]
        field_simp
      _ = a * (11 - 1)^2 + L := by norm_num
      _ = a * (11 + b / (2 * a))^2 + L := by
        congr
        rw [h_ab]
        field_simp
        norm_num
      _ = P 11 := by simp [hP_sq]
      _ = 181 := by rw [hP'']
  simp [hP] at habc₃
  ring_nf at habc₃
  -- calculate a, b, c using linarith
  have habc: a = 9/5 ∧ b = -18/5 ∧ c = 14/5 := by
    constructor
    any_goals constructor
    all_goals linarith
  simp [hP]
  -- plug in to compute target
  rw [habc.left, habc.right.left, habc.right.right]
  norm_num