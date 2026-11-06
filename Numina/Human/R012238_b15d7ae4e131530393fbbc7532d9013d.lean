import Mathlib

/-The positive integers $a, b, c, d$ satisfy $a>b>c>d, a+b+c+d=2010$ and $a^{2}-b^{2}+c^{2}-d^{2}=2010$. How many different sets of possible values of $(a, b, c, d)$ are there?-/
theorem  algebra_206520 : {(a, b, c, d) : ℤ × ℤ × ℤ × ℤ | a > b ∧ b > c ∧ c > d ∧ d > 0 ∧ a + b + c + d = 2010 ∧ a^2 - b^2 + c^2 - d^2 = 2010}.ncard = 501 := by
  have h1 : {(a, b, c, d) : ℤ × ℤ × ℤ × ℤ | a > b ∧ b > c ∧ c > d ∧ d > 0 ∧ a + b + c + d = 2010 ∧ a^2 - b^2 + c^2 - d^2 = 2010} = {(a, b, c, d) : ℤ × ℤ × ℤ × ℤ | 0 < d ∧ d < 502 ∧ a = 1005 - d ∧ b = 1004 - d ∧ c = d + 1} := by
    apply Set.ext
    simp
    intro a b c d
    constructor
    intro ⟨hab,hbc,hcd,hd0,hadd,hsq⟩
    -- We have $a-b \geq 1$ and $c-d \geq 1$.
    have hab' : 1 ≤ a - b := by linarith only [hab]
    have hcd' : 1 ≤ c - d := by linarith only [hcd]
    -- As $$ 2010=a^{2}-b^{2}+c^{2}-d^{2}=(a+b)(a-b)+(c+d)(c-d) \geq(a+b)+(c+d)=2010, $$ equality holds throughout and hence we must have $a-b=c-d=1$. 
    have h1 : a ^ 2 - b ^ 2 + c ^ 2 - d ^ 2 = (a+b)*(a-b)+(c+d)*(c-d) := by ring
    rw [← hsq, h1] at hadd
    apply le_iff_lt_or_eq.mp at hab'
    rcases hab' with hab' |hab'
    · nlinarith
    apply le_iff_lt_or_eq.mp at hcd'
    rcases hcd' with hcd'|hcd'
    · nlinarith
    -- This gives $(b+1)+b+(d+1)+d=2010$, or $b+d=1004$, where $b$ and $d$ are positive integers with $b \geq d+2$.
    have hbd : b + d = 1004 := by
      nlinarith
    have hbd' : d + 2 ≤ b := by nlinarith
    omega
    intro ⟨hd1,hd2,had,hbd,hcd⟩
    rw [had,hbd,hcd]
    ring_nf ;simp [hd1] ;linarith
  rw [h1]
  -- Hence we get 501 choices for $(b, d)$, namely, $(1003,1),(1002,2), \ldots,(503,501)$, and hence 501 choices for $(a, b, c, d)$, namely, $(1004,1003,2,1),(1003,1002,3,2), \ldots,(504$, $503,502,501)$.
  have h2 : {(a, b, c, d) : ℤ × ℤ × ℤ × ℤ | 0 < d ∧ d < 502 ∧ a = 1005 - d ∧ b = 1004 - d ∧ c = d + 1}.ncard = (↑(Finset.Icc 1 501) : Set ℕ).ncard := by
    refine Set.ncard_congr ?_ (fun a => ?_) ?_ ?_
    exact fun (a, b, c, d) ha => d.toNat
    simp ;omega
    simp
    intro a b c d a1 b1 c1 d1
    omega
    simp ;intro d hd1 hd2
    use (1005-(↑d:ℤ)),(1004-↑d),(↑d+1),(↑d)
    omega
  rw [h2,Set.ncard_coe_Finset] ;simp
    
      

      