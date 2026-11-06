import Mathlib

open Real

lemma lemma_1
    (u v : ℝ)
    (w : ℝ)
    (hu : 0 ≤ u)
    (hv : 0 ≤ v)
    (hw : 0 < w)
    (huv : u + v = 2 * w) :
    1 / (Real.sqrt u + Real.sqrt w) + 1 / (Real.sqrt v + Real.sqrt w) = 2 / (Real.sqrt u + Real.sqrt v) := by
  have h1 : 0 ≤ u := hu
  have h2 : 0 ≤ v := hv
  have h3 : 0 ≤ w := by linarith
  have h4 : Real.sqrt u ≥ 0 := Real.sqrt_nonneg u
  have h5 : Real.sqrt v ≥ 0 := Real.sqrt_nonneg v
  have h6 : Real.sqrt w ≥ 0 := Real.sqrt_nonneg w
  have h8 : Real.sqrt u + Real.sqrt w > 0 := by
    have h9 : Real.sqrt u ≥ 0 := Real.sqrt_nonneg u
    have h10 : Real.sqrt w > 0 := by
      apply Real.sqrt_pos.2
      linarith
    linarith
  have h10 : Real.sqrt v + Real.sqrt w > 0 := by
    have h11 : Real.sqrt v ≥ 0 := Real.sqrt_nonneg v
    have h12 : Real.sqrt w > 0 := by
      apply Real.sqrt_pos.2
      linarith
    linarith
  have h13 : Real.sqrt u + Real.sqrt v > 0 := by
    by_contra h
    push_neg at h
    have h14 : Real.sqrt u = 0 := by
      linarith [Real.sqrt_nonneg u, Real.sqrt_nonneg v, h]
    have h15 : Real.sqrt v = 0 := by
      linarith [Real.sqrt_nonneg u, Real.sqrt_nonneg v, h]
    have h16 : u = 0 := by
      calc
        u = (Real.sqrt u) ^ 2 := by rw [Real.sq_sqrt (show (0 : ℝ) ≤ u by linarith)]
        _ = 0 ^ 2 := by rw [h14]
        _ = (0 : ℝ) := by norm_num
    have h17 : v = 0 := by
      calc
        v = (Real.sqrt v) ^ 2 := by rw [Real.sq_sqrt (show (0 : ℝ) ≤ v by linarith)]
        _ = 0 ^ 2 := by rw [h15]
        _ = (0 : ℝ) := by norm_num
    have h18 : w = 0 := by
      nlinarith [huv, h16, h17]
    linarith
  have eq1 : 1 / (Real.sqrt u + Real.sqrt w) + 1 / (Real.sqrt v + Real.sqrt w) = 2 / (Real.sqrt u + Real.sqrt v) := by
    field_simp [Real.sqrt_nonneg u, Real.sqrt_nonneg v, Real.sqrt_nonneg w, h8, h10, h13]
    <;> nlinarith [Real.sqrt_nonneg u, Real.sqrt_nonneg v, Real.sqrt_nonneg w, sq_nonneg (Real.sqrt u - Real.sqrt v), sq_nonneg (Real.sqrt u - Real.sqrt w), sq_nonneg (Real.sqrt v - Real.sqrt w), Real.mul_self_sqrt (show 0 ≤ u by linarith), Real.mul_self_sqrt (show 0 ≤ v by linarith), Real.mul_self_sqrt (show 0 ≤ w by linarith), sq_nonneg (Real.sqrt u ^ 2 - Real.sqrt v ^ 2), sq_nonneg (Real.sqrt u ^ 2 - w), sq_nonneg (Real.sqrt v ^ 2 - w), huv, Real.sqrt_nonneg u, Real.sqrt_nonneg v, Real.sqrt_nonneg w]
  linarith [eq1]

theorem algebra_7319 :
    Set.ncard {x : ℤ | 0 ≤ x ∧ x ≤ 2014 ∧ 1 / (sqrt x + sqrt 1007) + 1 / (sqrt (2014 - x) + sqrt 1007) =
      2 / (sqrt x + sqrt (2014 - x))} = 2015 := by
  have h1 : {x : ℤ | 0 ≤ x ∧ x ≤ 2014 ∧ 1 / (sqrt x + sqrt 1007) + 1 / (sqrt (2014 - x) + sqrt 1007) =
      2 / (sqrt x + sqrt (2014 - x))} = Set.Icc (0 : ℤ) 2014 := by
    ext x 
    simp only [Set.mem_setOf_eq, Set.mem_Icc]
    constructor 
    · -- Assume x in the left side, need to show right
      rintro ⟨hx0, hx1, huv⟩ 
      exact ⟨hx0, hx1⟩
    · -- Assume x in right side, need to show left 
      rintro ⟨hx0, hx1⟩
      constructor 
      · -- Show 0 ≤ x
        exact hx0
      constructor 
      · -- Show x ≤ 2014
        exact hx1
      · -- Show the equation
        -- Note on application of lemma_1 :
        -- lemma_1 establishes the equation between 1 / (√x + √1007) + 1 / (√x + √(2014-x)) = 2 / (√x + √(2014-x))
        -- What we need: ∀x ∈ {0,1, ..., 2014}, equation holds
        have hx58 : 0 ≤ (x : ℝ) := by 
          exact_mod_cast show (0 : ℤ) ≤ x by omega 
        have hx58' : (x : ℝ) ≥ 0 := by 
          exact_mod_cast show (0 : ℤ) ≤ x by omega 
        have hx59 : (2014 - x : ℝ) ≥ 0 := by 
          have : (x : ℝ) ≤ (2014 : ℝ) := by 
            exact_mod_cast show x ≤ 2014 by omega 
          nlinarith 
        have h50 : (2014 - x : ℝ) ≥ 0 := by 
          have : (x : ℝ) ≤ (2014 : ℝ) := by 
            exact_mod_cast show x ≤ 2014 by omega 
          nlinarith 
        have h51 : (x : ℝ) + (2014 - x : ℝ) = 2 * (1007 : ℝ) := by
          nlinarith
        have h52 : (x : ℝ) + (2014 - x : ℝ) = 2 * (1007 : ℝ) := by
          nlinarith
        have hx60 : (1007 : ℝ) > 0 := by norm_num 
        have eq0 := lemma_1 (x : ℝ) (2014 - x : ℝ) (1007 : ℝ) 
          (by 
            have h38 : (x : ℝ) ≥ 0 := by 
              exact_mod_cast show (0 : ℤ) ≤ x by omega 
            nlinarith 
          ) 
          (by 
            have h39 : (2014 - x : ℝ) ≥ 0 := by
              have : (x : ℝ) ≤ (2014 : ℝ) := by 
                exact_mod_cast show x ≤ 2014 by omega 
              nlinarith
            exact_mod_cast h39 
          ) 
          (by norm_num) 
          (by 
            have h56 : (x : ℝ) + (2014 - x : ℝ) = (2014 : ℝ) := by 
              nlinarith 
            nlinarith 
          )
        norm_num at eq0 ⊢ 
        <;> try linarith [eq0]
        try nlinarith [eq0]
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp 
  all_goals try native_decide