import Mathlib

open Real
open scoped Real

theorem calculus_15667 (A B C : Real) (hA : A ∈ Set.Ioo 0 π)
  (hB : B ∈ Set.Ioo 0 π) (hC : C ∈ Set.Ioo 0 π) (hABC : A + B + C = π)
  (hC1 : C = π / 2) (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0)
  (h : a = sin A) (h' : b = sin B) (h'' : c = sin C) :
  arctan (a / (b + c)) + arctan (b / (a + c)) = π / 4 := by
  rcases hA with ⟨hA1, hA2⟩
  rcases hB with ⟨hB1, hB2⟩
  rcases hC with ⟨hC11, hC22⟩
  have hc1 : c = 1 := by
    rw [h'']
    rw [hC1]
    norm_num
  have hangle : A + B = π / 2 := by
    linarith [hABC, hC1]
  have hab : b = cos A := by
    have hsin : sin B = cos A := by
      have hB : B = π / 2 - A := by linarith [hangle]
      rw [hB]
      rw [Real.sin_pi_div_two_sub]
    rw [h']
    rw [hsin]
  have ha2 : a = sin A := by
    linarith [h]
  have h3 : a ^ 2 + b ^ 2 = 1 := by
    rw [ha2, hab]
    have hsin : sin A ^ 2 + cos A ^ 2 = 1 := Real.sin_sq_add_cos_sq A
    nlinarith [hsin]
  rw [hc1] at *
  have h4 : arctan (a / (b + 1)) + arctan (b / (a + 1)) = π / 4 := by
    have h5 : a / (b + 1) * (b / (a + 1)) < 1 := by
      have hn : a * b < (b + 1) * (a + 1) := by 
        nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 1), h3, ha, hb
          ]
      have h6 : a * b / ((b + 1) * (a + 1)) < 1 := by
        apply (div_lt_iff₀ (by positivity : 0 < (b + 1) * (a + 1)) ).mpr
        nlinarith
      have h7 : a / (b + 1) * (b / (a + 1)) = a * b / ((b + 1) * (a + 1)) := by
        field_simp
        <;> ring
      rw [h7]
      linarith [h6]
    have h8 : arctan (a / (b + 1)) + arctan (b / (a + 1)) = 
          arctan ( (a / (b + 1) + b / (a + 1)) / (1 - (a / (b + 1) * (b / (a + 1)) )) ) := by
      rw [arctan_add]
      all_goals
        all_goals linarith [h5]
    rw [h8]
    have h9 : (a / (b + 1) + b / (a + 1)) / (1 - (a / (b + 1) * (b / (a + 1)) )) = 1 := by
      have h11 : a / (b + 1) + b / (a + 1) = (1 + a + b) / ((b + 1) * (a + 1)) := by
        field_simp
        nlinarith [h3]
      have h12 : 1 - (a / (b + 1) * (b / (a + 1)) ) = (1 + a + b) / ((b + 1) * (a + 1)) := by
        field_simp
        nlinarith [h3]
      rw [h11, h12]
      field_simp
      <;> ring
    rw [h9]
    have h10 : arctan (1 : ℝ) = π / 4 := by
      rw [arctan_one]
    linarith [h10]
  linarith [h4]