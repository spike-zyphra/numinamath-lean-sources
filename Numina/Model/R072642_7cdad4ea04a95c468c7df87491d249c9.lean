import Mathlib

theorem number_theory_318880 (z : ℕ) (hz : z ∈ Finset.Icc 100000 999999) (h : (z / 1000) % 1000 = z % 1000) :
    11 ∣ z := by
  rw [Finset.mem_Icc] at hz
  rcases hz with ⟨hz1, hz2⟩
  have h2 : z = 1001 * (z / 1000) := by 
    omega
  rw [h2] at *
  have : 11 ∣ 1001 * (z / 1000) := by 
    have : 1001 * (z / 1000) = 11 * (91 * (z / 1000)) := by 
      omega
    rw [this]
    exact ⟨91 * (z / 1000), by ring⟩
  exact this