import Mathlib

/-- Show that if $\( a \)$ and $\( b \)$ are integers, then $\( a \equiv b \mod m \)$ if and only if there exists an integer $\( k \)$ such that $\( a = b + k m \)$.-/
theorem number_theory_4637
(m a b : ℤ):
a ≡ b [ZMOD m] ↔ ∃ k, a = b + k * m := by
  -- $a \equiv b [m]$ means that $a - b$ is divisible by m.
  rw [Int.modEq_iff_dvd]
  constructor <;> intro h
  · obtain ⟨k, hk⟩ := h
    exact ⟨-k, by linarith⟩
  · obtain ⟨k, hk⟩ := h
    exact ⟨-k, by linarith⟩