import Mathlib

theorem number_theory_32173 (Z : ℕ) (hZ : Z ∈ Finset.Icc 100000 999999) (hZ1 : (Z / 1000) % 1000 = (Z % 1000)) :
    11 ∣ Z := by
  rw [Finset.mem_Icc] at hZ
  rcases hZ with ⟨hZ2, hZ3⟩
  have h1 : Z = 1001 * (Z / 1000) := by
    omega
  rw [h1]
  omega