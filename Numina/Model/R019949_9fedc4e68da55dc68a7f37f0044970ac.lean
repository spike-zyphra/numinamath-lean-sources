import Mathlib

theorem algebra_296807 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a^2 + c^2 < b^2) (h1 : b = max (max a c) b) :
    ∃ x y, x ≠ y ∧ a * x^2 - Real.sqrt 2 * b * x + c = 0 ∧
    a * y^2 - Real.sqrt 2 * b * y + c = 0 := by 
  have h3 : b ^ 2 > 2 * (a * c) := by
    nlinarith [sq_nonneg (a - c), h]
  -- The discriminant of the quadratic $a x^2 - \sqrt{2} b x + c =0$ is $(sqrt(2)b)^2 - 4ac = 2b^2 - 4ac$. We need to show it's positive.
  have h4 : (Real.sqrt 2 * b) ^ 2 - 4 * a * c > 0 := by
    have h5 : (Real.sqrt 2 * b) ^ 2 = 2 * b^2 := by
      calc
        (Real.sqrt 2 * b) ^ 2 = (Real.sqrt 2) ^ 2 * b ^ 2 := by ring
        _ = 2 * b ^ 2 := by norm_num
    rw [h5]
    nlinarith
  use (Real.sqrt 2 * b + Real.sqrt ((Real.sqrt 2 * b) ^ 2 - 4 * a * c)) / (2 * a),
    (Real.sqrt 2 * b - Real.sqrt ((Real.sqrt 2 * b) ^ 2 - 4 * a * c)) / (2 * a)
  -- We now need to show that the roots are distinct
  have h5 : Real.sqrt ((Real.sqrt 2 * b) ^ 2 - 4 * a * c) > 0 := by
    have h6 : (Real.sqrt 2 * b) ^ 2 - 4 * a * c > 0 := by
      linarith
    have h7 : Real.sqrt ((Real.sqrt 2 * b) ^ 2 - 4 * a * c) ≥ 0 := by
      apply Real.sqrt_nonneg
    by_contra h8
    push_neg at h8
    have h8' : Real.sqrt ((Real.sqrt 2 * b) ^ 2 - 4 * a * c) = 0 := by
      linarith
    have h9 : (Real.sqrt 2 * b) ^ 2 - 4 * a * c = 0 := by
      calc
        (Real.sqrt 2 * b) ^ 2 - 4 * a * c = (Real.sqrt ((Real.sqrt 2 * b) ^ 2 - 4 * a * c)) ^ 2 := by
          rw [Real.sq_sqrt]
          nlinarith
        _ = 0 ^ 2 := by
          rw [h8']
        _ = 0 := by
          norm_num
    linarith
  constructor
  · -- Show that the two roots are different
    by_contra h_eq
    have : (Real.sqrt 2 * b + Real.sqrt ((Real.sqrt 2 * b) ^ 2 - 4 * a * c)) / (2 * a) =
        (Real.sqrt 2 * b - Real.sqrt ((Real.sqrt 2 * b) ^ 2 - 4 * a * c)) / (2 * a) := by
      linarith
    have : (Real.sqrt 2 * b + Real.sqrt ((Real.sqrt 2 * b) ^ 2 - 4 * a * c)) =
        (Real.sqrt 2 * b - Real.sqrt ((Real.sqrt 2 * b) ^ 2 - 4 * a * c)) := by
      have ha2 : 2 * a ≠ 0 := by nlinarith
      field_simp at this ⊢
      <;> nlinarith
    have h_eq2 : Real.sqrt ((Real.sqrt 2 * b) ^ 2 - 4 * a * c) = 0 := by
      nlinarith
    linarith
  constructor
  · -- Show that the first root is a solution
    have h6 : Real.sqrt ((Real.sqrt 2 * b) ^ 2 - 4 * a * c) ^ 2 = (Real.sqrt 2 * b) ^ 2 - 4 * a * c := by
      rw [Real.sq_sqrt]
      nlinarith
    have eq1 : a * ((Real.sqrt 2 * b + Real.sqrt ((Real.sqrt 2 * b) ^ 2 - 4 * a * c)) / (2 * a)) ^ 2
      - Real.sqrt 2 * b * ((Real.sqrt 2 * b + Real.sqrt ((Real.sqrt 2 * b) ^ 2 - 4 * a * c)) / (2 * a))
      + c = 0 := by
      field_simp
      nlinarith [h6, Real.sqrt_nonneg ((Real.sqrt 2 * b) ^ 2 - 4 * a * c), sq_nonneg (Real.sqrt ((Real.sqrt 2 * b) ^ 2 - 4 * a * c)), sq_nonneg (Real.sqrt 2 * b), Real.sqrt_nonneg ((Real.sqrt 2 * b) ^ 2 - 4 * a * c)]
    exact_mod_cast eq1
  · -- Show that the second root is a solution
    have h6 : Real.sqrt ((Real.sqrt 2 * b) ^ 2 - 4 * a * c) ^ 2 = (Real.sqrt 2 * b) ^ 2 - 4 * a * c := by
      rw [Real.sq_sqrt]
      nlinarith
    have eq2 : a * ((Real.sqrt 2 * b - Real.sqrt ((Real.sqrt 2 * b) ^ 2 - 4 * a * c)) / (2 * a)) ^ 2
      - Real.sqrt 2 * b * ((Real.sqrt 2 * b - Real.sqrt ((Real.sqrt 2 * b) ^ 2 - 4 * a * c)) / (2 * a))
      + c = 0 := by
      field_simp
      nlinarith [h6, Real.sqrt_nonneg ((Real.sqrt 2 * b) ^ 2 - 4 * a * c), sq_nonneg (Real.sqrt ((Real.sqrt 2 * b) ^ 2 - 4 * a * c)), sq_nonneg (Real.sqrt 2 * b), Real.sqrt_nonneg ((Real.sqrt 2 * b) ^ 2 - 4 * a * c)]
    exact_mod_cast eq2