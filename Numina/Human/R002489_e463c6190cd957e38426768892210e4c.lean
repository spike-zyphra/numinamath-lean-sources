import Mathlib 

/- A palindrome, such as 83438, is a number that remains the same when its digits are reversed. 
The numbers x and x+32 are three-digit and four-digit palindromes, respectively. 
What is the sum of the digits of x?
(A) 20
(B) 21
(C) 22
(D) 23
(E) 24 -/
theorem number_theory_94151 (x a b c d : ℕ) (hdig: a ≤ 9 ∧ b ≤ 9 ∧ c ≤ 9 ∧ d ≤ 9) 
(h₀ : x ≤ 999) (hx : x = a * 100 + b * 10 + a) (h₁ : x + 32 ≥ 1000) (htous: c ≠ 0) (hxp : x + 32 = c * 1000 + d * 100 + d * 10 + c): 
a + b + a = 24 := by
  obtain ⟨ha,hb,hc,hd⟩:=hdig
  --x+32 is at most 1031, which implies that the first digit is 1 and the second 0, forcing x+32=1001.
  have hh: x + 32 ≤ 1031 := by linarith
  have k : c = 1 ∧ d = 0 := by
    --assume the digits are not c=1 and d=0
    by_contra ll
    rw[Decidable.not_and_iff_or_not] at ll
    obtain ll1|ll2 := ll
    -- c≠1
    · have hhc : c = 0 ∨ c ≥ 2 := by omega
      obtain hhc1|hhc2 := hhc
      -- c=0 is not possible because x+32 must have four digits by hypothesis
      · rw[hhc1] at hxp
        contradiction
      -- c≥2 is not possible because x would have four digits as well which is contradiction
      · have k : c * 1000 + d * 100 + d * 10 + c > 2000 := by 
          calc
            c * 1000 + d * 100 + d * 10 + c = d * 100 + d * 10 + c + c * 1000 := by linarith
            d * 100 + d * 10 + c + c * 1000 > c * 1000 := by
              have hpos: d * 100 + d * 10 + c > 0 := by linarith
              apply lt_add_of_pos_left (c * 1000) hpos  
            _ ≥ 2000     := by linarith
        have kxp : x + 32 > 2000 := by rw[hxp]; exact k
        have cont : 999>1968 := by linarith
        contradiction
    -- d≠1
    · have hhd : d ≥ 1 := by omega
      have hhc : c ≥ 1 := by omega
      rw[hxp] at hh
      --we would have that the palindrome is greater than 1111 but contradicts the hypothesis x+32≤1031
      have hg : c * 1000 + d * 100 + d * 10 + c ≥ 1111 := by
        calc
          c * 1000 + d * 100 + d * 10 + c ≥ 1 * 1000 + 1 * 100 + 1 * 10 + 1 := by linarith
          _ = 1111 := by norm_num
      have cont : 1111 ≤ 1031 := by linarith
      contradiction 
  obtain ⟨hcc,hdd⟩:= k
  rw[hcc,hdd] at hxp
  ring_nf at hxp
  --then x=969 making a=9 and b=6
  have l : x = 969 := by linarith
  have hx_copy : x = a * 100 + b * 10 + a := by exact hx
  rw[l] at hx
  have ll : a = 9 ∧ b = 6 := by
    ring_nf at hx
    -- assume the digits are not a=9 and b=6
    by_contra k
    rw[Decidable.not_and_iff_or_not] at k
    obtain k1|k2 := k
    -- a≠9 is not possible because x+32 must have four digits by hypothesis
    · have j : a ≤ 8 := by omega
      have jj : a * 101 ≤ 808 := by
        calc a * 101 ≤ 8 * 101 := by gcongr
        _ = 808 := by norm_num 
      have jjj : 969 - a * 101 ≥ 100 := by linarith
      have hhx : 969 - a * 101 = b * 10 := by linarith
      rw[hhx] at jjj
      have hhb : b > 10 := by linarith
      have cont : 9 > 10 := by linarith
      contradiction
    -- b≠6
    · have hhb : b ≤ 5 ∨ b ≥ 7 := by omega
      obtain hhb1|hhb2 := hhb
      -- b≤5 is not possible because x+32 must have four digits by hypothesis
      · have contr : 969 < 959 := by linarith
        contradiction
      -- b≥7 is not possible because x would have four digits as well which is contradiction
      · rw[l] at hx_copy
        have contr : 899 ≥ a * 101 := by linarith
        have hha: a = 9 := by omega
        rw[hha] at contr
        contradiction
  --then sum the digits a+b+a
  obtain ⟨haa, hbb⟩:= ll
  rw[haa,hbb]