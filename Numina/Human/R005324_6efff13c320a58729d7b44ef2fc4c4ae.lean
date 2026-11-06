import Mathlib
set_option maxRecDepth 5000

def u : ℕ → ℕ
| 0 => 15
| 1 => 57
| n + 2 => u n + u (n + 1)

-- Auxiliary lemma: Prove periodicity modulo $9$.
lemma u_mod_9_period_8 (n : ℕ) : u (n + 8) ≡ u n [MOD 9] := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h_n : n < 8
    · -- For $n < 8$, compute directly.
      match n with
      | 0 => simp [u];exact Nat.ModEq.trans (by tauto) (Nat.ModEq.symm (by tauto))
      | 1 => simp [u];exact Nat.ModEq.trans (by tauto) (Nat.ModEq.symm (by tauto))
      | 2 => simp [u];exact Nat.ModEq.trans (by tauto) (Nat.ModEq.symm (by tauto))
      | 3 => simp [u];exact Nat.ModEq.trans (by tauto) (Nat.ModEq.symm (by tauto))
      | 4 => simp [u];exact Nat.ModEq.trans (by tauto) (Nat.ModEq.symm (by tauto))
      | 5 => simp [u];exact Nat.ModEq.trans (by tauto) (Nat.ModEq.symm (by tauto))
      | 6 => simp [u];exact Nat.ModEq.trans (by tauto) (Nat.ModEq.symm (by tauto))
      | 7 => simp [u];exact Nat.ModEq.trans (by tauto) (Nat.ModEq.symm (by tauto))
    · -- For $n ≥ 8$, use the recursive formula.
      have h_n': n ≥ 8 := by omega
      obtain ⟨m, hm⟩ := exists_add_of_le h_n'
      rw [hm]
      have h1 : u ((m + 8) + 8) = u (m + 15) + u (m + 14) := by
        have : u (m + 14 + 2) = u (m + 14) + u (m + 14 + 1) := by simp [u]
        have h₁: m + 14 + 2= (m + 8) + 8 := by ring
        have h₂: m + 14 + 1= m + 15 := by ring
        rw [add_comm (u (m + 14)), h₁, h₂] at this
        exact this
      have h2 : u (m + 8) = u (m + 7) + u (m + 6) := by
        have : u (m + 6 + 2) = u (m + 6) + u (m + 6 + 1) := by simp [u]
        have h₁: m + 6 + 2= m + 8 := by ring
        have h₂: m + 6 + 1= m + 7 := by ring
        rw [add_comm (u (m + 6)), h₁, h₂] at this
        exact this
      have h3 : u (m + 15) ≡ u (m + 7) [MOD 9] := by
        have : m + 7 < n:= by omega
        exact ih (m + 7) this
      have h4 : u (m + 14) ≡ u (m + 6) [MOD 9] := by
        have : m + 6 < n := by omega
        exact ih (m + 6) this
      rw [add_comm,← add_assoc] at h1
      rw [add_comm] at h2
      rw [h1, h2]
      apply Nat.ModEq.add
      · exact h3
      · exact h4

-- Auxiliary lemma: Extend modulo $9$ periodicity to any multiple of $8$.
lemma u_mod_9_period_8_multi (n k : ℕ) : u (n + k * 8) ≡ u n [MOD 9] := by
  induction k with
  | zero => exact Nat.ModEq.refl (u n)
  | succ k ih =>
    rw [Nat.succ_mul, ← add_assoc]
    have : u (n + k * 8 + 8) ≡ u (n + k * 8) [MOD 9] := u_mod_9_period_8 (n + k * 8)
    exact Nat.ModEq.trans this ih

/-On définit une suite ainsi:
$$
\left\{\begin{array}{l}
u_{0}=15, u_{1}=57 \\
u_{n}=u_{n-1}+u_{n-2} \text { pour tout } n \geq 2
\end{array}\right.
$$
Trouver le plus grand entier $k$ tel que $3^{k} \mid u_{2017}$.-/
theorem number_theory_607647 :
    IsGreatest {k | 0 ≤ k ∧ 3^k ∣ u 2017} 1 := by
  -- Prove $u_n$ divisible by $3$ for all $n$.
  have h_div_3 : ∀ n, 3 ∣ u n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
    match n with
    | 0 => simp [u]; norm_num
    | 1 => simp [u]; norm_num
    | n + 2 =>
      simp [u]
      have h1 : 3 ∣ u n := ih n (by omega)
      have h2 : 3 ∣ u (n + 1) := ih (n + 1) (by omega)
      exact dvd_add h1 h2

  -- Compute $u_2017$ mod $9$.
  have h_mod_9 : u 2017 ≡ 3 [MOD 9] := by
    have h_2017 : 2017 = 252 * 8 + 1 := by norm_num
    rw [h_2017]
    have h : u (252 * 8 + 1) ≡ u 1 [MOD 9] := by
      rw [Nat.add_comm]
      exact u_mod_9_period_8_multi 1 252
    have h_u1 : u 1 = 57 := by simp [u]
    have h_u1_mod_9 : u 1 ≡ 3 [MOD 9] := by decide
    exact Nat.ModEq.trans h h_u1_mod_9

  -- Prove $k = 1$ satisfies the condition.
  have h_in : 1 ∈ {k | 0 ≤ k ∧ 3^k ∣ u 2017} := by
    simp
    have h : u 2017 % 9 = 3 := by rw [h_mod_9]
    have : u 2017 % 3 = u 2017 % 9 % 3 := by omega
    rw [h] at this
    exact Nat.dvd_of_mod_eq_zero this

  -- Prove $k ≤ 1$ for all $k$ satisfying the condition.
  have h_greatest : ∀ k ∈ {k | 0 ≤ k ∧ 3^k ∣ u 2017}, k ≤ 1 := by
    intros k hk
    simp at hk
    rcases hk with ⟨h0, h_div⟩
    by_contra h_k_gt_1
    have h_k_ge_2 : k ≥ 2 := by omega
    have h_9_div : 3^2 ∣ 3^k := by
      exact Nat.pow_dvd_pow 3 h_k_ge_2
    have h_9 : 3^2 = 9 := by norm_num
    rw [h_9] at h_9_div
    have : 9 ∣ u 2017 := by
      have : 3^k ∣ u 2017 := by use h0
      apply dvd_trans h_9_div this
    have h_not_9 : ¬ 9 ∣ u 2017 := by
      rw [← Nat.modEq_zero_iff_dvd]
      have h_not_dvd: u 2017 % 9 = 3 := by
        rw [h_mod_9]
      intro h
      have h_dvd : u 2017 % 9 = 0 := by omega
      rw [h_dvd] at h_not_dvd
      linarith
    contradiction

  -- Combine above conditions to prove $k = 1$ is the greatest.
  exact ⟨h_in, h_greatest⟩
