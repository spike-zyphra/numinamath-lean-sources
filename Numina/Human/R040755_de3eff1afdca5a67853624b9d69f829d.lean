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
    have a_eq : a = 4 := by 
      have ha' : find_base [1,3,3,2,0,1] 2017 = some 4 := by rfl
      rw [←ha] at ha'
      exact Option.some.inj ha'
    have b_eq : b = 6 := by 
      have hb' : find_base [1,3,2,0,1] 2017 = some 6 := by rfl
      rw [←hb] at hb'
      exact Option.some.inj hb'
    have c_eq : c = 12 := by 
      have hc' : find_base [1,2,0,1] 2017 = some 12 := by rfl
      rw [←hc] at hc'
      exact Option.some.inj hc'
    rw [a_eq, b_eq, c_eq]
