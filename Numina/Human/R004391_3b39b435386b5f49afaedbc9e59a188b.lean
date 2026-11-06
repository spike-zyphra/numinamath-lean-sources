import Mathlib
import Init.Data.Nat.Basic

/- 34. De Morgan and Others. Mathematician Augustus De Morgan, who died in 1871, used to say that he was $x$ years old in the year $x^{2}$. Jasper Jenkins, wishing to outdo him, told me in 1925 that he was $\mathrm{a}^{2}+b^{2}$ years old in the year $\mathrm{a}^{4}+b^{4}$, that his age was $2 m$ in the year $2 m^{2}$, and finally, that he was $3 n$ years old in the year $3 n^{4}$.

In what year were De Morgan and Jenkins born? -/

theorem algebra_259829 :
    let E (year bday age : ℤ) : Prop
          := bday > 0 ∧ age > 0 ∧ year = bday + age
    let D (bday x : ℤ) : Prop := E (x^2) bday x
    let J₁ (bday a b : ℤ) : Prop := E (a^4 + b^4) bday (a^2 + b^2)
    let J₂ (bday m : ℤ) : Prop :=   E (2*(m^2)) bday (2*m)
    let J₃ (bday n : ℤ) : Prop :=   E (3*(n^4)) bday (3*n)
    -- De Morgan was born in 1806. When he was 43 years old,
    -- the current year equaled the square of his age: $43^2 = 1849$.
    (D 1806 43) ∧ (let bday : ℤ := 1860
      -- Jenkins was born in 1860.
      -- He was $5^2 + 6^2 = 61$ years old in the $5^4 + 6^4 = 1921$ year.
      (J₁ bday 5 6) ∧
      -- In the $2 \times 31^2 = 1922$ year, he turned $2 \times 31 = 62$ years old.
      (J₂ bday 31) ∧
      -- Finally, his age was $3 \times 5 = 15$ years in the $3 \times 5^4 = 1875$ year.
      (J₃ bday 5)) := by
  intro E D J₁ J₂ J₃
  constructor
  . simp [D, E]
  . intro bday
    exact ⟨by simp [E, J₁, bday],
           by simp [E, J₂, bday],
           by simp [E, J₃, bday]⟩