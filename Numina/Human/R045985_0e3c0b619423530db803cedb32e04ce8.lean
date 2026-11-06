import Mathlib

theorem Nat.div_eq_iff : ∀ {k x y : ℕ}, 0 < k → (x / k = y ↔ x ≤ y * k + k - 1 ∧ y * k ≤ x) := by sorry

/- The function $\mathrm{f}$ on the positive integers satisfies $\mathrm{f}(1)=1, \mathrm{f}(2 \mathrm{n}+1)=\mathrm{f}(2 \mathrm{n})+1$ and $\mathrm{f}(2 \mathrm{n})=3$ $f(n)$. Find the set of all $m$ such that $m=f(n)$ for some $n$. -/
theorem number_theory_604317 (f : ℕ → ℕ) (f1 : f 1 = 1) (fodd : ∀ n, 0 < n → f (2 * n + 1) = f (2 * n) + 1)
(feven : ∀ n, 0 < n → f (2 * n) = 3 * f n) : {m | 0 < m ∧ ∃ n, 0 < n ∧ m = f n} =
{m | 0 < m ∧ ¬(2 ∈ Nat.digits 3 m)} := by
-- According to the reference answer, define a new function $g$ to be "writing $n$ in base $2$ then reads it in base $3$"
  simp [Set.ext_iff]; let g : ℕ → ℕ := fun n => Nat.ofDigits 3 (Nat.digits 2 n)
-- Prove that $g$ has exactly the same properties as $f$ does
  have g1 : g 1 = 1 := by simp [g]
  have godd : ∀ n, 0 < n → g (2 * n + 1) = g (2 * n) + 1 := by
    intro n npos; simp [g, Nat.ofDigits_cons, add_comm]
    rw [show (1+2*n)/2 = n by simp [Nat.div_eq_iff]; ring_nf; simp]
    nth_rw 3 [show 2 = 2^1 by simp]; rw [Nat.digits_base_pow_mul, Nat.ofDigits_append]
    simp; simp; exact npos
  have geven : ∀ n, 0 < n → g (2 * n) = 3 * g n := by
    intro n npos; simp [g];nth_rw 2 [show 2 = 2^1 by simp]
    rw [Nat.digits_base_pow_mul, Nat.ofDigits_append]; simp; simp; exact npos
-- Use parity induction Nat.evenOddStrongRec on n to show that $f$ and $g$ are the same
  have feqg : ∀ n, 0 < n → f n = g n := by
    intro n; induction n using Nat.evenOddStrongRec with
    | h_even n ihn =>
      intro npos; simp at npos; rw [feven, geven]; simp; apply ihn
      simp [two_mul]; any_goals exact npos
    | h_odd n ihn =>
      intro; by_cases hn : n ≤ 0
      · simp at hn; simp [hn, f1, g1]
      push_neg at hn; simp [fodd n hn, godd n hn]; apply ihn; simp; positivity
-- Split "iff" and use $f=g$ to rewrite the final goals
  intro m mpos; constructor
  · rintro ⟨n, npos, hn⟩; rw [feqg n npos] at hn; simp [g] at hn
  -- Use properties of Nat.digits and Nat.ofDigits to prove the "if" part
    rw [hn, Nat.digits_ofDigits]; intro h
    have := Nat.digits_lt_base (show 1<2 by simp) h; any_goals linarith
    intro l hl; have := Nat.digits_lt_base (show 1<2 by simp) hl; linarith
    intro; apply Nat.getLast_digit_ne_zero; positivity
-- To prove the "only if" part, we revert the construction of $g$
-- use $Nat.ofDigits 2 (Nat.digits 3 m)$ to fulfill the existence goal and prove it satisfies the desired properties
  intro h; use Nat.ofDigits 2 (Nat.digits 3 m)
  have hpos : 0 < Nat.ofDigits 2 (Nat.digits 3 m) := by
    by_contra!; simp at this; apply_fun fun t => Nat.digits 2 t at this
    rw [Nat.digits_ofDigits, Nat.digits_zero, Nat.digits_eq_nil_iff_eq_zero] at this
    linarith; simp; intro l hl; have := Nat.digits_lt_base (show 1<3 by simp) hl
    interval_cases l; simp; simp; contradiction
    intro; apply Nat.getLast_digit_ne_zero; positivity
  constructor; exact hpos; rw [feqg _ hpos]; simp [g]
  rw [Nat.digits_ofDigits, Nat.ofDigits_digits]; simp
  intro l hl; have := Nat.digits_lt_base (show 1<3 by simp) hl
  interval_cases l; simp; simp; contradiction
  intro; apply Nat.getLast_digit_ne_zero; positivity