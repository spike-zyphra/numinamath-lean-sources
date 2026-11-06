import Mathlib

open Nat Finset

/- Show that if \( n \) is a composite integer with \( n \neq 4 \), then \( (n-1)! \equiv 0 \mod n \).-/
theorem number_theory_4786 {n : ℕ} (hn : n ≠ 4) (hcom : ∃ a b, n = a * b ∧ a ∈ Ioo 1 n ∧ b ∈ Ioo 1 n) :
    n ∣ (n - 1) ! := by
  /- 原答案错误，以下为重写的正确证明。 -/
  rcases hcom with ⟨a, b, hab, ha, hb⟩
  simp at ha hb
  /- 按`a=b`与`a≠b`分类讨论-/
  rcases eq_or_ne a b with h | h
  . /- `a=b` -/
    have ha' : 4 < a * a := by
      rw [lt_iff_le_and_ne]
      constructor
      nlinarith
      symm
      rwa [hab, ← h] at hn
    /- 因为`n≠4`，所以`2*a<n`。 -/
    have hn' : 2 * a < n := by nlinarith
    /- 进而由`a*a ∣ (2*a)!`和`(2*a)! ∣ (n-1)!`可知`a*a ∣ (n-1)!`。 -/
    trans (2*a)!
    . have : (2*a) * a ∣ (2*a)! := by
        have : 2*a=(2*a-1)+1 := by
          symm
          exact Nat.sub_add_cancel (by linarith)
        rw [this, Nat.factorial_succ]
        apply Nat.mul_dvd_mul_left
        apply Nat.dvd_factorial
        linarith
        linarith
      rw [mul_assoc] at this
      convert dvd_of_mul_left_dvd this
      rw [hab, h]
    apply Nat.factorial_dvd_factorial
    exact le_sub_one_of_lt hn'
  /- `a≠b` -/
  /- 当`0<a<b`时有`a*b ∣ b!`。 -/
  have H {a b : ℕ} (ha : 0 < a) (hab : a < b) : a*b ∣ b ! := by
    rw [mul_comm, ← @Nat.sub_add_cancel b 1 (by linarith), Nat.factorial_succ]
    apply Nat.mul_dvd_mul_left
    apply Nat.dvd_factorial
    . exact ha
    . exact Nat.le_sub_one_of_lt hab
  rcases lt_trichotomy a b with h | h | h
  . /- `a<b` -/
    trans (b !)
    . rw [hab]
      exact H (by linarith) (by linarith)
    apply Nat.factorial_dvd_factorial
    exact Nat.le_sub_one_of_lt hb.2
  . contradiction -- `a=b`与`a≠b`矛盾！
  . /- `b<a` -/
    trans (a !)
    . rw [hab, mul_comm]
      exact H (by linarith) (by linarith)
    apply Nat.factorial_dvd_factorial
    exact Nat.le_sub_one_of_lt ha.2
