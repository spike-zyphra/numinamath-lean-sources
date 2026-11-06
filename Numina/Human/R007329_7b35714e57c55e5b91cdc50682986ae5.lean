import Mathlib

/-In parallelogram $PQRS$, the measure of angle $P$ is five times the measure of angle $Q$. What is the measure of angle $R$, in degrees?-/
theorem algebra_20583 {P Q R S : ℝ} (hP : P ∈ Set.Ioo 0 180)
    (hQ : Q ∈ Set.Ioo 0 180) (hR : R ∈ Set.Ioo 0 180) (hS : S ∈ Set.Ioo 0 180)
    (hPS : P + S = 180) (hQR : Q + R = 180) (hPQ : P = 5 * Q) (hPR : P = R):
    R = 150 := by
      linarith