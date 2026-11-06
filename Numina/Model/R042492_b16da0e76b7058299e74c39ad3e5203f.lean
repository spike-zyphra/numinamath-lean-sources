import Mathlib
open Real
theorem algebra_215065 (x y z : ℝ) (h1 : sin (x + y + z) = 9 / 41) (h2 : cos x * cos y * cos z = 5 / 41) :
tan x * tan y + tan y * tan z + tan z * tan x = -7 ∨ tan x * tan y + tan y * tan z + tan z * tan x = 9:= by
  have h3 : cos (x + y + z) ^ 2 + sin (x + y + z) ^ 2 = 1 := by 
    exact Real.cos_sq_add_sin_sq (x + y + z)
  rw [h1] at h3 
  have h4 : cos (x + y + z) ^ 2 = 1600 / 1681 := by
    nlinarith 
  have h5 : cos (x + y + z) = 40 / 41 ∨ cos (x + y + z) = -40 / 41 := by
    have h6 : cos (x + y + z) ^ 2 - (40 / 41) ^ 2 = 0 := by 
      nlinarith [h4]
    have h7 : (cos (x + y + z) - 40 / 41) * (cos (x + y + z) + 40 / 41) = 0 := by
      nlinarith [h6]
    cases' (mul_eq_zero.mp h7) with h8 h9
    · left
      linarith
    · right
      linarith
  have eq1 : sin (x + y + z) = sin x * cos y * cos z + cos x * sin y * cos z + cos x * cos y * sin z - sin x * sin y * sin z := by 
    rw [show x + y + z = (x + y) + z by ring]
    rw [sin_add]
    rw [sin_add, cos_add]
    ring_nf 
  have eq2 : cos (x + y + z) = cos x * cos y * cos z - sin x * sin y * cos z - sin x * cos y * sin z - cos x * sin y * sin z := by 
    rw [show x + y + z = (x + y) + z by ring]
    rw [cos_add]
    rw [cos_add, sin_add]
    ring_nf 
  cases h5 with
  | inl h5 =>
    have h6 : sin x * sin y * cos z + sin x * cos y * sin z + cos x * sin y * sin z = -35 / 41 := by
      rw [eq2] at h5 
      nlinarith 
    have htan : tan x * tan y + tan y * tan z + tan z * tan x =
        (sin x * sin y * cos z + sin x * cos y * sin z + cos x * sin y * sin z) / (cos x * cos y * cos z) := by 
      have ht1 : tan x * tan y = (sin x * sin y * cos z) / (cos x * cos y * cos z) := by 
        rw [tan_eq_sin_div_cos, tan_eq_sin_div_cos]
        have hcosx : cos x ≠ 0 := by 
          by_contra h
          have hcosx : cos x = 0 := by linarith 
          have h2' : cos x * cos y * cos z = 0 := by 
            rw [hcosx]
            norm_num 
          linarith [h2]
        have hcosy : cos y ≠ 0 := by
          by_contra h
          have hcosy : cos y = 0 := by linarith 
          have h2' : cos x * cos y * cos z = 0 := by 
            rw [hcosy]
            norm_num 
          linarith [h2]
        have hcosz : cos z ≠ 0 := by 
          by_contra h
          have hcosz : cos z = 0 := by linarith 
          have h2' : cos x * cos y * cos z = 0 := by 
            rw [hcosz]
            norm_num 
          linarith [h2]
        field_simp [hcosx, hcosy, hcosz]
        <;> ring 
      have ht2 : tan y * tan z = (sin y * sin z * cos x) / (cos x * cos y * cos z) := by 
        rw [tan_eq_sin_div_cos, tan_eq_sin_div_cos]
        have hcosx : cos x ≠ 0 := by 
          by_contra h
          have hcosx : cos x = 0 := by linarith 
          have h2' : cos x * cos y * cos z = 0 := by 
            rw [hcosx]
            norm_num 
          linarith [h2]
        have hcosy : cos y ≠ 0 := by 
          by_contra h
          have hcosy : cos y = 0 := by linarith 
          have h2' : cos x * cos y * cos z = 0 := by 
            rw [hcosy]
            norm_num 
          linarith [h2]
        have hcosz : cos z ≠ 0 := by 
          by_contra h
          have hcosz : cos z = 0 := by linarith 
          have h2' : cos x * cos y * cos z = 0 := by 
            rw [hcosz]
            norm_num 
          linarith [h2]
        field_simp [hcosx, hcosy, hcosz]
        <;> ring 
      have ht3 : tan z * tan x = (sin z * sin x * cos y) / (cos x * cos y * cos z) := by 
        rw [tan_eq_sin_div_cos, tan_eq_sin_div_cos]
        have hcosx : cos x ≠ 0 := by 
          by_contra h
          have hcosx : cos x = 0 := by linarith 
          have h2' : cos x * cos y * cos z = 0 := by 
            rw [hcosx]
            norm_num 
          linarith [h2]
        have hcosy : cos y ≠ 0 := by 
          by_contra h
          have hcosy : cos y = 0 := by linarith 
          have h2' : cos x * cos y * cos z = 0 := by 
            rw [hcosy]
            norm_num 
          linarith [h2]
        have hcosz : cos z ≠ 0 := by 
          by_contra h
          have hcosz : cos z = 0 := by linarith 
          have h2' : cos x * cos y * cos z = 0 := by 
            rw [hcosz]
            norm_num 
          linarith [h2]
        field_simp [hcosx, hcosy, hcosz]
        <;> ring 
      rw [show tan x * tan y + tan y * tan z + tan z * tan x = tan x * tan y + tan y * tan z + tan z * tan x by rfl]
      rw [ht1, ht2, ht3]
      <;> field_simp 
      <;> ring 
    left 
    rw [htan]
    have h7 : cos x * cos y * cos z = 5 / 41 := by 
      linarith 
    rw [h7]
    field_simp at *
    nlinarith [h6]
  | inr h5 =>
    have h6 : sin x * sin y * cos z + sin x * cos y * sin z + cos x * sin y * sin z = 45 / 41 := by 
      rw [eq2] at h5 
      nlinarith 
    have htan : tan x * tan y + tan y * tan z + tan z * tan x =
        (sin x * sin y * cos z + sin x * cos y * sin z + cos x * sin y * sin z) / (cos x * cos y * cos z) := by 
      have ht1 : tan x * tan y = (sin x * sin y * cos z) / (cos x * cos y * cos z) := by 
        rw [tan_eq_sin_div_cos, tan_eq_sin_div_cos]
        have hcosx : cos x ≠ 0 := by 
          by_contra h
          have hcosx : cos x = 0 := by linarith 
          have h2' : cos x * cos y * cos z = 0 := by 
            rw [hcosx]
            norm_num 
          linarith [h2]
        have hcosy : cos y ≠ 0 := by
          by_contra h
          have hcosy : cos y = 0 := by linarith 
          have h2' : cos x * cos y * cos z = 0 := by 
            rw [hcosy]
            norm_num 
          linarith [h2]
        have hcosz : cos z ≠ 0 := by 
          by_contra h
          have hcosz : cos z = 0 := by linarith 
          have h2' : cos x * cos y * cos z = 0 := by 
            rw [hcosz]
            norm_num 
          linarith [h2]
        field_simp [hcosx, hcosy, hcosz]
        <;> ring 
      have ht2 : tan y * tan z = (sin y * sin z * cos x) / (cos x * cos y * cos z) := by 
        rw [tan_eq_sin_div_cos, tan_eq_sin_div_cos]
        have hcosx : cos x ≠ 0 := by 
          by_contra h
          have hcosx : cos x = 0 := by linarith 
          have h2' : cos x * cos y * cos z = 0 := by 
            rw [hcosx]
            norm_num 
          linarith [h2]
        have hcosy : cos y ≠ 0 := by 
          by_contra h
          have hcosy : cos y = 0 := by linarith 
          have h2' : cos x * cos y * cos z = 0 := by 
            rw [hcosy]
            norm_num 
          linarith [h2]
        have hcosz : cos z ≠ 0 := by 
          by_contra h
          have hcosz : cos z = 0 := by linarith 
          have h2' : cos x * cos y * cos z = 0 := by 
            rw [hcosz]
            norm_num 
          linarith [h2]
        field_simp [hcosx, hcosy, hcosz]
        <;> ring 
      have ht3 : tan z * tan x = (sin z * sin x * cos y) / (cos x * cos y * cos z) := by 
        rw [tan_eq_sin_div_cos, tan_eq_sin_div_cos]
        have hcosx : cos x ≠ 0 := by 
          by_contra h
          have hcosx : cos x = 0 := by linarith 
          have h2' : cos x * cos y * cos z = 0 := by 
            rw [hcosx]
            norm_num 
          linarith [h2]
        have hcosy : cos y ≠ 0 := by 
          by_contra h
          have hcosy : cos y = 0 := by linarith 
          have h2' : cos x * cos y * cos z = 0 := by 
            rw [hcosy]
            norm_num 
          linarith [h2]
        have hcosz : cos z ≠ 0 := by 
          by_contra h
          have hcosz : cos z = 0 := by linarith 
          have h2' : cos x * cos y * cos z = 0 := by 
            rw [hcosz]
            norm_num 
          linarith [h2]
        field_simp [hcosx, hcosy, hcosz]
        <;> ring 
      rw [show tan x * tan y + tan y * tan z + tan z * tan x = tan x * tan y + tan y * tan z + tan z * tan x by rfl]
      rw [ht1, ht2, ht3]
      <;> field_simp 
      <;> ring
    right 
    rw [htan]
    have h7 : cos x * cos y * cos z = 5 / 41 := by 
      linarith 
    rw [h7]
    field_simp at *
    nlinarith [h6]