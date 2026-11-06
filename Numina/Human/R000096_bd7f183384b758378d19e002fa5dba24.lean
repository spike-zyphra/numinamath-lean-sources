import Mathlib

/- Fibonacci sequence -/
def u_4547 : ℕ → ℕ
| 0 => 0
| 1 => 1
| n + 2 => u_4547 n + u_4547 (n + 1)

/- Show that the sequence \( u_n \) is even if and only if \( n \) is divisible by 3. -/
theorem number_theory_4547 (n) : Even (u_4547 n) ↔ 3 ∣ n :=
  -- This is an inductive proof
  match n with
  -- check base case n=0
  | 0 => by simp [u_4547]
  -- check base case n=1
  | 1 => by simp [u_4547]
  | n + 2 => by
    simp only [u_4547]
    -- prove by cases
    have mod : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases mod with mod | mod | mod
    -- n % 3 = 0
    · have h₁ := number_theory_4547 n |>.mpr (by omega)
      have h₂ := number_theory_4547 (n + 1) |>.not.mpr (by omega)
      rw [Nat.not_even_iff_odd] at h₂
      exact iff_of_false (by simpa using Even.add_odd h₁ h₂) (by omega)
    -- n % 3 = 1
    · have h₁ := number_theory_4547 n |>.not.mpr (by omega)
      have h₂ := number_theory_4547 (n + 1) |>.not.mpr (by omega)
      rw [Nat.not_even_iff_odd] at h₁ h₂
      exact iff_of_true (by simpa using Odd.add_odd h₁ h₂) (by omega)
    -- n % 3 = 2
    · have h₁ := number_theory_4547 n |>.not.mpr (by omega)
      have h₂ := number_theory_4547 (n + 1) |>.mpr (by omega)
      rw [Nat.not_even_iff_odd] at h₁
      exact iff_of_false (by simpa using Odd.add_even h₁ h₂) (by omega)
