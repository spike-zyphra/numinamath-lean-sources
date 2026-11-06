import Mathlib

theorem algebra_227887 {bread_price bread_mass shoe_mass : ℝ} 
    (hm : shoe_mass = 0.75 * bread_mass) (hbm : bread_mass > 0)
    (hp : shoe_price = 1.2 * bread_price) (hbp : bread_price > 0) :
    let bread_consumed := 0.85 * bread_mass
    let shoe_consumed := shoe_mass
    let ratio := (shoe_price / shoe_consumed) / (bread_price / bread_consumed)
    (ratio - 1) * 100 = 36 := by
  simp only [hp, hm]
  have h1 : bread_mass > 0 := hbm
  have h2 : bread_price > 0 := hbp
  have h3 : (0.85 * bread_mass) > 0 := by
    apply mul_pos
    norm_num
    all_goals linarith
  have h4 : (0.75 * bread_mass) > 0 := by
    apply mul_pos
    norm_num
    all_goals linarith
  have eq3 : ( ((1.2 * bread_price) / (0.75 * bread_mass) ) / ( bread_price / (0.85 * bread_mass) ) ) = (1.36 : ℝ) := by
    have h7 : ( ((1.2 * bread_price) / (0.75 * bread_mass) ) / ( bread_price / (0.85 * bread_mass) ) ) = ( (1.2 * bread_price) * (0.85 * bread_mass) ) / ( (0.75 * bread_mass) * bread_price ) := by 
      field_simp [show bread_price ≠ 0 by linarith, show bread_mass ≠ 0 by linarith, show (0.85 * bread_mass) ≠ 0 by positivity, show (0.75 * bread_mass) ≠ 0 by positivity]
      <;> ring
    rw [h7]
    have h8 : ( (1.2 * bread_price) * (0.85 * bread_mass) ) / ( (0.75 * bread_mass) * bread_price ) = (1.36 : ℝ) := by
      have h9 : ( (1.2 * bread_price) * (0.85 * bread_mass) ) = (1.02) * ( bread_price * bread_mass ) := by ring
      have h10 : ( (0.75 * bread_mass) * bread_price ) = (0.75) * ( bread_price * bread_mass ) := by ring
      rw [h9, h10]
      have h11 : bread_price * bread_mass > 0 := mul_pos h2 h1
      have h12 : ( (1.02 : ℝ) * ( bread_price * bread_mass ) ) / ( (0.75 : ℝ) * ( bread_price * bread_mass ) ) = (1.36 : ℝ) := by
        have h13 : ( (1.02 : ℝ) * ( bread_price * bread_mass ) ) / ( (0.75 : ℝ) * ( bread_price * bread_mass ) ) =
            (1.02 / 0.75 : ℝ) := by
          field_simp [h11]
          <;> ring
        rw [h13]
        norm_num
      linarith
    linarith
  rw [eq3]
  all_goals norm_num