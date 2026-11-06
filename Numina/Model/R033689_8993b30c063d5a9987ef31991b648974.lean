import Mathlib

def Nat.p_dvd (p : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 =>
    if (p + 2) ∣ (n + 1) then
      Nat.p_dvd p ((n + 1) / (p + 2))
    else
      n + 1
decreasing_by
  have h : 0 < p + 2 := by linarith [p]
  apply (Nat.div_lt_iff_lt_mul h).2
  simp; ring_nf; linarith [p]

theorem Nat.p_dvd_decrease (p : ℕ) (n : ℕ) : ∀ m ≤ n, Nat.p_dvd p m ≤ m := by
  induction n with
  | zero => intro m hm; simp at hm; rw [hm]; simp [Nat.p_dvd]
  | succ n hn =>
    intro m hm
    by_cases hm' : m = n + 1
    · rw [hm']
      by_cases hp : (p + 2) ∣ (n + 1)
      · simp [Nat.p_dvd, hp]
        calc
          p.p_dvd ((n + 1) / (p + 2)) ≤ (n + 1) / (p + 2) := by
            apply hn; apply Nat.le_of_lt_succ; simp; apply Nat.div_lt_self; linarith [n]; linarith [p]
          _ ≤ n + 1 := by apply Nat.div_le_self
      · simp [Nat.p_dvd, hp]
    · have hm'' : m ≤ n := by apply Nat.le_of_lt_succ; simp; apply Nat.lt_of_le_of_ne hm hm'
      apply hn; exact hm''

def primeFactorList : ℕ → List ℕ
  | 0 => []
  | 1 => []
  | k + 2 =>
    let m := Nat.minFac (k + 2)
    m :: primeFactorList (Nat.p_dvd (m - 2) (k + 2))
decreasing_by
  have h1 : m ∣ (k + 2) := by apply Nat.minFac_dvd
  have h2 : Nat.Prime m := by simp [m]; apply Nat.minFac_prime; apply ne_of_gt; linarith [k]
  have h3 : 2 ≤ m ∧ m.minFac = m := by apply Nat.prime_def_minFac.1 h2
  simp [Nat.p_dvd, h3.1, h1]; ring_nf
  calc
    ((2 + k).minFac - 2).p_dvd ((2 + k) / (2 + k).minFac) ≤ (2 + k) / (2 + k).minFac := by
      apply Nat.p_dvd_decrease ((2 + k).minFac - 2) ((2 + k) / (2 + k).minFac) ((2 + k) / (2 + k).minFac); rfl
    _ < 2 + k := by apply Nat.div_lt_self; linarith [k]; rw [add_comm]; linarith [h3.2]

#eval primeFactorList 39
#eval primeFactorList 55
#eval primeFactorList 66
#eval primeFactorList 117
#eval primeFactorList 132
#eval primeFactorList 198


theorem Numbeer_Theory_609050 {n : ℕ} (hn1 : 1 ≤ n) (hn2 : n ≤ 200) (hn3 : (primeFactorList n).sum = 16) :
  n = 39 ∨ n = 55 ∨ n = 66 ∨ n = 117 ∨ n = 132 ∨ n = 198 := by 
  interval_cases n <;> norm_num [primeFactorList, Nat.p_dvd] at hn3 ⊢ <;> tauto