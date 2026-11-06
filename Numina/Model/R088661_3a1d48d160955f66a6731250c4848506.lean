import Mathlib

theorem algebra_275961 {a b c P : ℝ} (hP : P = (a + b + c) / 2) :
    ((P - a) + (P - b)) ^ 3 = (P - a) ^ 3 + (P - b) ^ 3 + 3 * (P - a) * (P - b) * c := by
  have h1 : (P - a) + (P - b) = c := by
    rw [hP]
    ring
  rw [h1]
  -- Now need to express $c^3$ as $(P - a)^3 + (P - b)^3 + 3 * (P - a) * (P - b) * c$
  -- We know that $c = (P - a) + (P - b)$ from the previous proof, so we can use the expansion formula.
  have h3 : c = (P - a) + (P - b) := by linarith
  rw [h3]
  -- Now we need to expand $((P - a) + (P - b))^3$ using the formula $(x + y)^3 = x^3 + y^3 + 3xy(x + y)$
  ring_nf