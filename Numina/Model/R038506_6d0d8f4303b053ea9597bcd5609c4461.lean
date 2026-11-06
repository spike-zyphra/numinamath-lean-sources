import Mathlib

open Nat

namespace number_theory_134915

def a (n : ℕ) : ℤ := match n with
| 0 => 0
| 1 => 1
| n + 2 => 4 * a (n + 1) - a n

def b (n : ℕ) : ℤ := match n with
| 0 => 1
| 1 => 2
| n + 2 => 4 * b (n + 1) - b n

end number_theory_134915

open number_theory_134915

theorem number_theory_134915 (n : ℕ) : (b n)^2 = 3 * (a n)^2 + 1 := by

  let P (n : ℕ) := (b n) ^ 2 = 3 * (a n) ^ 2 + 1 ∧ (b (n + 1)) * (b n) = 2 + 3 * (a (n + 1)) * (a n)

  have h1 : ∀ (n : ℕ), P n := by
    intro n
    induction' n using Nat.strongRecOn with n ih
    cases n with
    | zero =>
      simp [P, b, a]
    | succ n =>
      cases n with
      | zero =>
        simp [P, b, a]
      | succ n =>
        have h3 := ih n (by omega)
        have h4 := ih (n + 1) (by omega)
        simp [P, b, a] at h3 h4 ⊢
        rcases h3 with ⟨ha1, hb1⟩
        rcases h4 with ⟨ha2, hb2⟩
        ring_nf at ha1 hb1 ha2 hb2 ⊢
        constructor
        · nlinarith [ha1, hb1, ha2, hb2]
        · nlinarith [ha1, hb1, ha2, hb2]

  have h4 : P n := h1 n
  exact (h4).1