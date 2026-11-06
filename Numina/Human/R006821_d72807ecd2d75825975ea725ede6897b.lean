import Mathlib

open Finset 

theorem number_theory_641466 (k : ℤ) (A : ℤ → ℤ) (hA : ∀ k, A k = 489 + k * 1958)
  (n : ℕ) (hn : 1 ≤ n) :
  1958 ∣ (A k)^n - 445^n - 44^n := by 
  have eq1 : A k ^ n - 445 ^ n - 44 ^ n = 
    A k ^ n - (445 ^ n + 44 ^ n) := by ring_nf
  rw [eq1]
  apply Int.ModEq.dvd
  have akmodeq : A k ^ n ≡ 489 ^ n [ZMOD 1958] := by
    refine Int.ModEq.pow n ?_
    rw [hA]
    refine Int.ModEq.symm ((fun {a b n} => Int.modEq_iff_add_fac.mpr) ?_)
    use k
    ring
  have modeq : 445 ^ n + 44 ^ n ≡ 489 ^ n [ZMOD 1958] := by 
    have aux1 : (489 : ℤ) = 445 + 44 := by norm_num
    rw [aux1, add_pow]
    apply Int.modEq_of_dvd
    have aux2 : ∑ m ∈ Finset.range (n + 1), (445 : ℤ) ^ m * 44 ^ (n - m) * ↑(n.choose m) - (445 ^ n + 44 ^ n) = 
      ∑ m ∈ Ico 1 n, (445 : ℤ) ^ m * 44 ^ (n - m) * ↑(n.choose m) := by
      have insert1 : range (n + 1) = insert n (Ico 0 n) := by 
        refine Finset.ext_iff.mpr ?_
        intro x
        constructor
        · intro hx 
          simp at hx
          simp
          omega
        · intro hx
          simp at hx
          simp
          omega
      have insert2 : Ico 0 n = insert 0 (Ico 1 n) := by
        exact Eq.symm (Nat.Ico_insert_succ_left hn)
      rw [insert1, sum_insert, insert2, sum_insert]
      simp
      simp
      simp
    rw [aux2]
    apply dvd_sum
    intro i hi
    simp at hi
    obtain ⟨hi1, hi2⟩ := hi
    have ige1 : i ≥ 1 := by 
      linarith
    have nige1 : n - i ≥ 1 := by 
      omega
    have aux3 : (445 : ℤ) ^ i * 44 ^ (n - i) = 
      (445 : ℤ) ^ (i - 1 + 1) * 44 ^ ((n - i - 1) + 1) := by 
      have aux4 : n - i = (n - i - 1) + 1 := by
        omega
      have aux5 : i = i - 1 + 1 := by
        omega
      nth_rw 1 [aux5]
      nth_rw 1 [aux4]
    rw [aux3]
    rw [pow_add, pow_add]
    have aux6 : (445 : ℤ) ^ (i - 1) * 445 ^ 1 * (44 ^ (n - i - 1) * 44 ^ 1) * ↑(n.choose i) =(445 * 44) * ((445 : ℤ) ^ (i - 1) * 44 ^ (n - i - 1) * ↑(n.choose i)) := by 
      ring
    rw [aux6]
    have dvd1 : 1958 ∣ (445 * 44: ℤ) := by
      omega
    exact Dvd.dvd.mul_right dvd1 (445 ^ (i - 1) * 44 ^ (n - i - 1) * ↑(n.choose i))
  exact Int.ModEq.symm (Int.ModEq.trans akmodeq (id (Int.ModEq.symm modeq)))