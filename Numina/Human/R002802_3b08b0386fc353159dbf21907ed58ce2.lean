import Mathlib

/- 2. Bear Big and Bear Small agreed to climb Baiyun Mountain along the same route on the weekend. They started from the foot of the mountain at the same time and immediately went down after reaching the top. Both of their downhill speeds were twice their respective uphill speeds, and Bear Big was faster than Bear Small. After 2 hours of departure, Bear Big and Bear Small met 1600 meters away from the top; when Bear Small reached the top, Bear Big had just descended to the halfway point. How many hours did Bear Big spend from departure to returning to the foot of the mountain? -/
theorem algebra_115493 {H t₁ t₂ v V x : ℝ}
  (hpos : V > 0)
  (hpos' : t₁ > 0)
  (h₁ : V * t₁ = H) -- t₁: time for Bear Big to summit
  (h₂ : 2 * V * (2 - t₁) = 1600)
  (h₃ : 2 * v = H - 1600)
  (h₄ : v * t₂ = H) -- t₂ : time for Bear Small to summit
  (h₅ : 2 * V * (t₂ - t₁) = H / 2)
  (h₆ : x = t₁ + H / (2 * V))
  : x = 14/5 := by
  -- Eliminate H
  rw [h₆]
  have hv : H / V = t₁
  · field_simp; rw [mul_comm]; exact h₁.symm
  rw [mul_comm, ←div_div, hv]
  field_simp at h₅
  have ht12 : t₂ = 5 / 4 * t₁
  · have : 2 * (t₂ - t₁) = H / V / 2
    · field_simp
      linarith [h₅]
    rw [hv] at this
    linarith [this]
  -- Eliminate V
  have hVv : V = 5/4 * v
  · have : V * t₁ = v * t₂
    · trans H; exact h₁; exact h₄.symm
    rw [ht12] at this
    nlinarith [this]
  rw [hVv] at h₂
  rw [ht12] at h₄
  rw [←h₄] at h₃
  ring_nf at h₃
  have hvt : v * t₁ = 8/5 * v + 1280
  · linarith [h₃]
  ring_nf at h₂
  rw [hvt] at h₂
  -- Eliminate v
  have hv : v = 4800
  · linarith [h₂]
  rw [hv] at h₃
  -- Solve for t₁
  linarith