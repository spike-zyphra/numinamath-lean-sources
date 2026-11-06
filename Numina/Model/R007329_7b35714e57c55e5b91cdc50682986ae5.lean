import Mathlib

theorem algebra_20583 {P Q R S : ℝ} (hP : P ∈ Set.Ioo 0 180)
    (hQ : Q ∈ Set.Ioo 0 180) (hR : R ∈ Set.Ioo 0 180) (hS : S ∈ Set.Ioo 0 180)
    (hPS : P + S = 180) (hQR : Q + R = 180) (hPQ : P = 5 * Q) (hPR : P = R):
    R = 150 := by
  rcases hP with ⟨hP1, hP2⟩
  rcases hQ with ⟨hQ1, hQ2⟩
  rcases hR with ⟨hR1, hR2⟩
  rcases hS with ⟨hS1, hS2⟩
  have h1 : R = 5 * Q := by 
    linarith [hPQ, hPR]
  rw [h1] at hQR 
  -- Substitute angle r = 5 * q into angle q + angle r = 180
  -- Then angle q + angle 5 * q = 180
  -- Then 6 * q = 180, angle q = 30
  have h4 : Q = 30 := by 
    linarith
  -- From h1: angle r = 5 * angle q. angle q = 30, so angle r = 150
  have h2 : R = 150 := by
    linarith [h4, h1]
  exact h2