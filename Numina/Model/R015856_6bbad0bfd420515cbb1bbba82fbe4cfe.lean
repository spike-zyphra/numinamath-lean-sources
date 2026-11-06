import Mathlib

theorem algebra_234400 {x : ℕ} (hx : x ≠ 0) (h1 : (1 - 1 / 16 : ℚ) * x = (1 - 1 / 15 : ℚ) * (x - 2000)) :
    x = 544000 := by
  have eq1 : (15/16 : ℚ) * x = (14/15 : ℚ) * (x - 2000) := by 
    norm_num at h1 ⊢
    linarith
  -- Multiply through by 240 to clear denominators
  -- left side: (15/16)x *240 = 15*15x = 225x
  -- right side: (14/15)(x-2000)*240 =14*16(x-2000) = 224(x - 2000)
  -- Therefore: 225x = 224(x - 2000) => 225x = 224x - 224*2000 => x = -448000
  have eq2 : (x : ℚ) = -448000 := by 
    linarith
  have h2 : (x : ℚ) ≥ 0 := by
    exact_mod_cast (show (x : ℕ) ≥ 0 by omega)
  linarith