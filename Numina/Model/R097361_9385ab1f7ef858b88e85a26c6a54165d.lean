import Mathlib

theorem algebra_6332 {a b c : ℝ} (ha : a^2 ≠ b^2) (f : ℝ → ℝ)
    (h : ∀ x, a * f (x - 1) + b * f (1 - x) = c * x) :
    f = fun x => (c / (a - b)) * x + (c / (a + b)) := by

  funext x

  have eq1 := h (x + 1)
  have eq2 := h (1 - x)
  simp [show x + 1 - 1 = x by ring, show 1 - (x + 1) = -x by ring] at eq1
  simp [show (1 - x) - 1 = -x by ring, show 1 - (1 - x) = x by ring] at eq2

  have eq3 : a * f x + b * f (-x) = c * (x + 1) := by linarith
  have eq4 : b * f x + a * f (-x) = c * (1 - x) := by linarith

  have eq5 : f x = (c / (a - b)) * x + (c / (a + b)) := by 
    have eq6 : (a ^ 2 - b ^ 2) * f x = a * c * (x + 1) - b * c * (1 - x) := by
      have eq7 : a * f x + b * f (-x) = c * (x + 1) := by linarith
      have eq8 : b * f x + a * f (-x) = c * (1 - x) := by linarith
      have eq9 : (a ^ 2 - b ^ 2) * f x = a * c * (x + 1) - b * c * (1 - x) := by
        calc
          (a ^ 2 - b ^ 2) * f x = a * (a * f x + b * f (-x)) - b * (b * f x + a * f (-x)) := by ring_nf
          _ = a * (c * (x + 1)) - b * (c * (1 - x)) := by rw [eq7, eq8]
          _ = (a * c * (x + 1) - b * c * (1 - x)) := by ring
      linarith
    field_simp [(show a - b ≠ 0 by
      intro h1
      have h2 : a^2 = b^2 := by
        have h3 : a = b := by linarith
        rw [h3]
        <;> nlinarith
      contradiction
      ), (show a + b ≠ 0 by
        intro h1
        have h2 : a^2 = b^2 := by
          have h3 : a = -b := by linarith
          rw [h3]
          <;> nlinarith
        contradiction
      )] 
    <;> nlinarith
  exact eq5