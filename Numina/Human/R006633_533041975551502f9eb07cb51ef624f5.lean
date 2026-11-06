import Mathlib

lemma l_dvd_mul_right_of_dvd {a b : Nat} (h : a ∣ b) (c : Nat) : a ∣ b * c :=
  Nat.dvd_trans h (Nat.dvd_mul_right _ _)

lemma l_dvd_mul_left_of_dvd {a b : Nat} (h : a ∣ b) (c : Nat) : a ∣ c * b :=
  Nat.dvd_trans h (Nat.dvd_mul_left _ _)


/- Let $p_1$ and $p_2$ be distinct prime numbers. Let $N = p_1 p_2$.
Let $X_0$ be the least positive integer that has exactly $N$ distinct positive divisors. (It is known that $X_0 = 2^{\max(p_1,p_2)-1} \cdot 3^{\min(p_1,p_2)-1}$.)
Suppose $X_0$ is written in the form $m \cdot 6^k$, where $m$ and $k$ are positive integers and $6$ is not a divisor of $m$.
Show that the sum $m+k$ is equal to $2^{|p_1-p_2|} + \min(p_1,p_2) - 1$. -/
theorem number_theory_639475
  {p1 p2 : ℕ}
  (hp1 : p1.Prime) (hp2 : p2.Prime) (hne : p1 ≠ p2)
  (N : ℕ) (hN : N = p1 * p2)
  (X : ℕ)
  (hX : IsLeast {x | 0 < x ∧ x.divisors.card = N} X)
  (hX' : X = 2 ^ (max p1 p2 - 1) * 3 ^ (min p1 p2 - 1))
  (m k : ℕ) (hm : 0 < m) (hk : 0 < k)
  (hX' : X = m * 6 ^ k) (mdvd : ¬(6 ∣ m))
  : m + k = 2 ^ ((p1 : ℤ) - p2).natAbs + min p1 p2 - 1 :=
by
  let pl := max p1 p2
  let ps := min p1 p2
  have pls : pl > ps := by
    omega
  let A := pl - 1
  let B := ps - 1
  have XAB : X = 2 ^ A * 3 ^ B := by
    simp [A, B, pl, ps]
    omega
  have rX : X = m * 2 ^ k * 3 ^ k := by
    rw [mul_assoc]
    rw [←mul_pow]
    simp
    assumption
  have : A > B := by
    simp [A, B]
    have : ps > 0 := by
      simp [ps]
      constructor
      . exact Nat.Prime.pos hp1
      . exact Nat.Prime.pos hp2
    omega
  have : B ≥ k := by
    by_contra h
    simp at h
    rw [rX] at XAB
    have : 3 ^ k ∣ m * 2 ^ k * 3 ^ k := by
      exact Nat.dvd_mul_left (3 ^ k) (m * 2 ^ k)
    have : ¬ 3 ^ k ∣ 2 ^ A * 3 ^ B := by
      intro H
      have : 3 ^ k ∣ 3 ^ B := by
        apply Nat.Coprime.dvd_of_dvd_mul_left ?_ H
        exact Nat.Coprime.pow k A rfl
      have : k ≤ B := by
        exact Nat.pow_dvd_pow_iff_le_right'.mp this
      omega
    apply this
    rw [←XAB]
    assumption
  have : A ≥ k := by
    by_contra h
    simp at h
    rw [rX] at XAB
    have : 3 ^ k ∣ m * 2 ^ k * 3 ^ k := by
      exact Nat.dvd_mul_left (3 ^ k) (m * 2 ^ k)
    have : ¬ 3 ^ k ∣ 2 ^ A * 3 ^ B := by
      intro H
      have : 3 ^ k ∣ 3 ^ B := by
        apply Nat.Coprime.dvd_of_dvd_mul_left ?_ H
        exact Nat.Coprime.pow k A rfl
      have : k ≤ B := by
        exact Nat.pow_dvd_pow_iff_le_right'.mp this
      omega
    apply this
    rw [←XAB]
    assumption
  have mAB : m = 2 ^ (A - k) * 3 ^ (B - k) := by
    rw [rX] at XAB
    apply_fun (fun x => x / 3 ^ k) at XAB
    rw [Nat.mul_div_assoc] at XAB
    rw [Nat.div_self] at XAB
    rw [Nat.mul_div_assoc] at XAB
    rw [Nat.pow_div] at XAB
    simp at XAB
    apply_fun (fun x => x / 2 ^ k) at XAB
    rw [Nat.mul_div_assoc] at XAB
    rw [Nat.div_self] at XAB
    simp at XAB
    rw [mul_comm, Nat.mul_div_assoc] at XAB
    rw [Nat.pow_div] at XAB
    rw [mul_comm]
    assumption
    assumption
    simp
    apply Nat.pow_dvd_pow_iff_le_right'.mpr
    assumption
    exact Nat.two_pow_pos k
    simp
    assumption
    simp
    apply Nat.pow_dvd_pow_iff_le_right'.mpr
    assumption
    exact Nat.pos_of_neZero (3 ^ k)
    simp
  have : A = k ∨ B = k := by
    by_contra h
    simp at h
    have : A > k ∧ B > k := by
      constructor
      <;> omega
    apply mdvd
    rw [show 6 = 2 * 3 by simp]
    refine Nat.Coprime.mul_dvd_of_dvd_of_dvd rfl ?_ ?_
    rw [mAB]
    refine l_dvd_mul_right_of_dvd ?_ (3 ^ (B - k))
    refine Dvd.dvd.pow ?_ ?_
    simp
    omega
    rw [mAB]
    refine l_dvd_mul_left_of_dvd ?_ (2 ^ (A - k))
    refine Dvd.dvd.pow ?_ ?_
    simp
    omega
  have : B = k := by
    by_contra h
    have : A = k := by
      tauto
    subst this
    omega
  subst this
  simp at *
  simp [A, B] at mAB
  have : pl - 1 - (ps - 1) = pl - ps := by omega
  rw [this] at mAB
  subst mAB
  simp [B]
  rw [Nat.add_sub_assoc]
  congr
  omega
  omega
