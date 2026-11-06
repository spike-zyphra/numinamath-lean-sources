import Mathlib

/-Déterminer tous les couples d'entiers positifs ou nuls $(x, y)$ pour lesquels $x^{2}+y^{2}$ divise à la fois $x^{3}+y$ et $x+y^{3}$.-/
theorem number_theory_604721 (x y : ℕ) : ((x ^ 2 + y ^ 2) ∣ (x ^ 3 + y) ∧ (x ^ 2 + y ^ 2) ∣ (x + y ^ 3)) ↔
(x = 0 ∧ y = 0) ∨ (x = 1 ∧ y = 0) ∨ (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 1) := by
-- Assume w. l. o. g. that $x$ is less or equal to $y$
  wlog xley : x ≤ y
  · specialize this y x (by omega)
    rw [add_comm, and_comm]; nth_rw 2 [add_comm]; nth_rw 4 [add_comm]; rw [this]
    constructor; all_goals intro h; rcases h with ⟨_,_⟩|⟨_,_⟩|⟨_,_⟩|⟨_,_⟩; all_goals simp_all
  constructor
  -- If $y$ is less than $2$, then we trivially get all the solutions listed in the final goal
  · rintro ⟨hdvd1, hdvd2⟩; by_cases ybd : y < 2
    · interval_cases y; all_goals simp_all
      interval_cases x; all_goals omega
  -- If $x$ is less than $1$, then we quickly reach a contradiction from $y^2$ divides $y$
    by_cases xbd : x < 1
    · simp_all; nth_rw 2 [show y = y^1 by simp] at hdvd1
      rw [Nat.pow_dvd_pow_iff_le_right] at hdvd1; all_goals omega
    push_neg at ybd xbd
  -- Rewrite $x$ and $y$ to multiples of their gcd respectively
    obtain ⟨X, Y, ⟨copr, hX, hY⟩⟩ := Nat.exists_coprime x y
    let hdvd1' := hdvd1; let hdvd2' := hdvd2
  -- Rewrite the two division assumption hdvd1' and hdvd2' in terms of $x.gcd y$, $X$ and $Y$
    rw [hX] at hdvd1' hdvd2'; nth_rw 2 4 [hY] at hdvd1' hdvd2'; ring_nf at hdvd1' hdvd2'
    rw [mul_comm, ← Nat.mul_add, pow_two, mul_assoc] at hdvd1' hdvd2'
    rw [show X^3*x.gcd y^3+x.gcd y*Y = x.gcd y*(x.gcd y^2*X^3+Y) by ring] at hdvd1'
    rw [show X*x.gcd y+x.gcd y^3*Y^3 = x.gcd y*(X+x.gcd y^2*Y^3) by ring] at hdvd2'
    rw [Nat.mul_dvd_mul_iff_left] at hdvd1' hdvd2'
  -- Prove that $x.gcd y$ divides $Y$
    replace hdvd1' : x.gcd y ∣ Y := by
      have := dvd_trans (show x.gcd y ∣ x.gcd y * (X ^ 2 + Y ^ 2) by simp) hdvd1'
      rw [← Nat.dvd_add_iff_right] at this; exact this
      rw [pow_two, mul_assoc]; simp
  -- Prove that $x.gcd y$ divides $X$
    replace hdvd2' : x.gcd y ∣ X := by
      have := dvd_trans (show x.gcd y ∣ x.gcd y * (X ^ 2 + Y ^ 2) by simp) hdvd2'
      rw [← Nat.dvd_add_iff_left] at this; exact this
      rw [pow_two, mul_assoc]; simp
  -- Prove that $x.gcd y$ equals $1$ and use this to simplify assumptions
    have hgcd : x.gcd y = 1 := by
      rw [Nat.coprime_iff_gcd_eq_one] at copr; rw [← Nat.dvd_one, ← copr, Nat.dvd_gcd_iff]
      exact And.intro hdvd2' hdvd1'
    simp [hgcd] at hX hY; rw [← hX, ← hY] at copr
  -- According to the reference answer, we need further prove the following division relation
    have auxdvd : x ^ 2 + y ^ 2 ∣ x * y - 1 := by
      suffices : x ^ 2 + y ^ 2 ∣ x ^ 2 * (x * y - 1)
      · rw [Nat.Coprime.dvd_mul_left] at this; exact this
        rw [Nat.coprime_self_add_left, Nat.coprime_pow_left_iff, Nat.coprime_pow_right_iff]
        rw [Nat.coprime_comm]; exact copr; all_goals norm_num
      calc
        _ ∣ y * (x ^ 3 + y) - (x ^ 2 + y ^ 2) := by
          apply Nat.dvd_sub'; exact Nat.dvd_trans hdvd1 (show (x ^ 3 + y) ∣ y * (x ^ 3 + y) by simp)
          rfl
        _ = _ := by
          zify; rw [Nat.cast_sub, Nat.cast_sub]; push_cast; ring
          rw [show 1 = 1*1 by simp]; apply mul_le_mul; any_goals omega
          rw [Nat.mul_add, ← pow_two, add_le_add_iff_right, show 3 = 1+2 by simp, pow_add]
          rw [← mul_assoc, pow_one]; apply Nat.le_mul_of_pos_left; positivity
  -- Apply Nat.le_of_dvd to auxdvd, then prove the reversed inequality to reach a contradiction
    apply Nat.le_of_dvd at auxdvd; suffices : x * y - 1 < x ^ 2 + y ^ 2; omega; calc
      _ < x * y := by apply Nat.sub_lt; positivity; simp
      _ ≤ y ^ 2 := by rw [pow_two, mul_le_mul_right]; all_goals omega
      _ < _ := by simp; apply Nat.pow_pos; omega
    rw [Nat.sub_pos_iff_lt, ← Nat.add_one_le_iff, show 1+1 = 1*2 by simp]; apply mul_le_mul
    any_goals omega
    all_goals apply Nat.gcd_pos_of_pos_left; omega
-- Conversely, it is straightforward to check that the listed values satisfy the two division relations
  intro h; rcases h with ⟨_,_⟩|⟨_,_⟩|⟨_,_⟩|⟨_,_⟩; all_goals simp_all