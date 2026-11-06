import Mathlib 

open List Nat

namespace Number_Theory_609613

open List

-- give a definition of how to find this base
-- this take some times
def find_base (digits : List ℕ) (decimal_val : ℕ) : Option ℕ :=
  find? (fun a => Nat.ofDigits a (digits.reverse)  = decimal_val) (List.range 100)

end Number_Theory_609613

open Number_Theory_609613

theorem Number_Theory_609613 {a b c : ℕ} (ha : some a = find_base [1,3,3,2,0,1] 2017) 
  (hb : some b = find_base [1,3,2,0,1] 2017) (hc : some c = find_base [1,2,0,1] 2017) :
  a + b + c = 22 := by 
  have ha1 : a = 4 := by
    have h1 : some a = find_base [1, 3, 3, 2, 0, 1] 2017 := ha
    have h2 : find_base [1, 3, 3, 2, 0, 1] 2017 = some 4 := by
      unfold find_base
      native_decide
    rw [h2] at h1
    have h3 : a = 4 := by
      simp at h1 ⊢
      all_goals try { tauto }
      all_goals try { omega }
    exact h3
  have hb1 : b = 6 := by
    have h1 : some b = find_base [1, 3, 2, 0, 1] 2017 := hb
    have h2 : find_base [1, 3, 2, 0, 1] 2017 = some 6 := by
      unfold find_base
      native_decide
    rw [h2] at h1
    have h3 : b = 6 := by
      simp at h1 ⊢
      all_goals try { tauto }
      all_goals try { omega }
    exact h3
  have hc1 : c = 12 := by
    have h1 : some c = find_base [1, 2, 0, 1] 2017 := hc
    have h2 : find_base [1, 2, 0, 1] 2017 = some 12 := by
      unfold find_base
      native_decide
    rw [h2] at h1
    have h3 : c = 12 := by
      simp at h1 ⊢
      all_goals try { tauto }
      all_goals try { omega }
    exact h3
  omega