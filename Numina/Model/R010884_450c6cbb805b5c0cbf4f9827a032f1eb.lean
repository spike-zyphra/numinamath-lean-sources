import Mathlib

theorem algebra_20617 (hour : Fin 12 → Fin 60 → Fin 720) (minute : Fin 60 → Fin 720) (degree : Fin 720 → ℚ)
    (hour_def : ∀ h, ∀ m, hour h m = h.val * 60 + m.val)
    (minute_def : ∀ m, minute m = m.val * 12)
    (degree_def : ∀ d, degree d = if d ≤ 360 then d.val / 2 else 360 - d.val / 2) :
    degree (hour 4 20 - minute 20) = 10 := by
  have h1 : hour 4 20 = 260 := by
    simp [hour_def]
    <;> native_decide
  have h2 : minute 20 = 240 := by 
    simp [minute_def]
    <;> native_decide
  have h3 : hour 4 20 - minute 20 = 20 := by 
    rw [h1, h2]
    native_decide
  rw [h3]
  simp [degree_def]
  <;> native_decide