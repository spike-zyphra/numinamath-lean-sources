import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat

/- Let x, y, z be three positive integers with gcd(x,y,z)=1. If x | yz(x+y+z), y | xz(x+y+z),
z | xy(x+y+z), and x + y + z | xyz show that xyz(x+y+z) is a perfect square -/
theorem number_theory_8850
  (x y z : ℕ)
  (h₀ : 0 < x)
  (h₁ : 0 < y)
  (h₂ : 0 < z)
  (h₃ : Nat.gcd (Nat.gcd x y) z = 1)
  (h₄ : x ∣ y * z * (x + y + z))
  (h₅ : y ∣ x * z * (x + y + z))
  (h₆ : z ∣ x * y * (x + y + z))
  (h₇ : (x + y + z) ∣ x * y * z) :
  ∃ n, n^2 = x * y * z * (x + y + z) := by {
    -- suffices to prove each prime's multiplicity in (x*y*z*(x+y+z) is even
    suffices h : ∀ p : ℕ , Nat.Prime p → Even ((x*y*z*(x+y+z)).factorization p) by {
      -- prove auxiliary inequalities
      have hnz : x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 ∧ x+y+z ≠ 0 := by
        constructor
        all_goals omega
      rcases hnz with ⟨hxnz, hynz, hznz, hxyznz⟩
      let a := x*y*z*(x+y+z)
      -- use n = ∏ p ∈ a.primeFactors, p ^ (a.factorization p / 2)
      use ∏ p ∈ a.primeFactors, p ^ (a.factorization p / 2)
      rw [← Finset.prod_pow]
      simp_rw [← pow_mul]
      -- prove auxiliary equations of prime factors of a
      have hmid : ∀ x ∈ a.primeFactors, x^(a.factorization x / 2 * 2) = x^(a.factorization x) := by {
        intro x hx
        specialize h x (prime_of_mem_primeFactors hx)
        rw [Nat.div_mul_cancel (even_iff_two_dvd.mp h)]
      }
      -- substitute to find a square
      rw [Finset.prod_congr _ hmid, ← Nat.prod_factorization_eq_prod_primeFactors (.^.)]
      rw [factorization_prod_pow_eq_self]
      -- prove some remain inequality
      repeat rw [Nat.mul_ne_zero_iff]
      tauto
      rfl
    }
    intro p hp

    -- case 0: none of x, y, z is divided by p
    have hc0 (h: (¬ p ∣ x)∧(¬ p ∣ y)∧(¬ p ∣ z)) : Even ((x*y*z*(x+y+z)).factorization p) := by {
      rcases h with ⟨hx, hy, hz⟩
      -- use x + y + z | xyz to show that p not divide x+y+z
      have hxyz : ¬ p ∣ x+y+z := by {
        intro h
        have hmid : p ∣ x*y*z := Nat.dvd_trans h h₇
        exact (Nat.Prime.not_dvd_mul hp (Nat.Prime.not_dvd_mul hp hx hy) hz) hmid
      }
      -- suffices to show that the multiplicity of p in (x * y * z * (x + y + z)) is 0
      suffices h: (x * y * z * (x + y + z)).factorization p = 0 by {
        exact ZMod.eq_zero_iff_even.mp (congrArg Nat.cast h)
      }
      -- suffices to show that ¬ p ∣ x * y * z * (x + y + z)
      suffices h: ¬ p ∣ x * y * z * (x + y + z) by {
        exact factorization_eq_zero_of_not_dvd h
      }
      exact (Nat.Prime.not_dvd_mul hp (Nat.Prime.not_dvd_mul hp (Nat.Prime.not_dvd_mul hp hx hy) hz) hxyz)
    }

    -- case 1: p divides exactly one of x, y, z
    -- wlog, assume p | x
    have hc1 (x y z: ℕ) (h₀: 0 < x) (h₁: 0 < y) (h₂: 0 < z) (h₃ : (x.gcd y).gcd z = 1) (h₄ : x ∣ y * z * (x + y + z)) (h₅ : y ∣ x * z * (x + y + z)) (h₆ : z ∣ x * y * (x + y + z)) (h₇ : x + y + z ∣ x * y * z) (h: (p ∣ x)∧(¬ p ∣ y)∧(¬ p ∣ z)) : Even ((x*y*z*(x+y+z)).factorization p) := by {
      -- prove auxiliry inequalities
      have hnz : x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 ∧ x+y+z ≠ 0 := by
        constructor
        all_goals omega
      rcases hnz with ⟨hxnz, hynz, hznz, hxyznz⟩
      have hprodnz : x*y*z ≠ 0 := by {
        repeat rw [Nat.mul_ne_zero_iff]
        exact ⟨⟨hxnz, hynz⟩, hznz⟩
      }
      rcases h with ⟨hx, hy, hz⟩

      apply even_iff_two_dvd.mpr
      -- show x.factorization p ≤ (y*z*(x+y+z)).factorization p from x | y*z*(x+y+z)
      have hm₁ : x.factorization p ≤ (y*z*(x+y+z)).factorization p := by {
        have hnz : y*z*(x+y+z) ≠ 0 := mul_ne_zero_iff.mpr ⟨(mul_ne_zero_iff.mpr ⟨hynz, hznz⟩), hxyznz⟩
        exact (Nat.factorization_le_iff_dvd hxnz hnz).mpr h₄ p
      }
      -- decomposite (y*z*(x+y+z)).factorization p to eliminate the 0 part
      have hm₂ : (y*z*(x+y+z)).factorization p = (x+y+z).factorization p := by {
        rw [factorization_mul _ _, factorization_mul _ _]
        simp
        exact ⟨factorization_eq_zero_of_not_dvd hy, factorization_eq_zero_of_not_dvd hz⟩
        · exact hynz
        · exact hznz
        · exact Nat.mul_ne_zero hynz hznz
        · exact hxyznz
      }
      rw [hm₂] at hm₁
      -- show (x+y+z).factorization p ≤ (x*y*z).factorization p from x+y+z | x*y*z
      have hm₃ : (x+y+z).factorization p ≤ (x*y*z).factorization p := (Nat.factorization_le_iff_dvd hxyznz hprodnz).mpr h₇ p
      -- eliminate the 0 part to find (x*y*z).factorization p = x.factorization p
      have hm₄ : (x*y*z).factorization p = x.factorization p := by {
        repeat rw [factorization_mul]
        simp
        rw [factorization_eq_zero_of_not_dvd hy, factorization_eq_zero_of_not_dvd hz]
        simp
        · exact hxnz
        · exact hynz
        · exact Nat.mul_ne_zero hxnz hynz
        · exact hznz
      }
      rw [hm₄] at hm₃
      -- show that x.factorization p = (x + y + z).factorization p
      have hm : x.factorization p = (x + y + z).factorization p := by exact Nat.le_antisymm hm₁ hm₃
      -- substitue to find (x*y*z*(x+y+z)).factorization p is 2*(x.factorization p), then it's even
      have hm' := calc
        (x*y*z*(x+y+z)).factorization p = x.factorization p + y.factorization p + (x+y+z).factorization p := by {
          repeat rw [factorization_mul]
          simp
          exact factorization_eq_zero_of_not_dvd hz
          -- prove remaining inequalities
          · exact hxnz
          · exact hynz
          · exact Nat.mul_ne_zero hxnz hynz
          · exact hznz
          · exact hprodnz
          · exact hxyznz
        }
        _ = x.factorization p + (x+y+z).factorization p := by {rw [factorization_eq_zero_of_not_dvd hy]; simp}
        _ = 2*(x.factorization p) := by {rw [← hm]; ring}
      omega
    }

    -- case 2: p divides exactly two of x, y, z
    -- wlog: assume p | x, p | y
    have hc2 (x y z: ℕ) (h₀: 0 < x) (h₁: 0 < y) (h₂: 0 < z) (h₃ : (x.gcd y).gcd z = 1) (h₄ : x ∣ y * z * (x + y + z)) (h₅ : y ∣ x * z * (x + y + z)) (h₆ : z ∣ x * y * (x + y + z)) (h₇ : x + y + z ∣ x * y * z) (h: (p ∣ x)∧( p ∣ y)∧(¬ p ∣ z)) : Even ((x*y*z*(x+y+z)).factorization p) := by {
      -- prove some auxiliry inequalities
      have hnz : x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 ∧ x+y+z ≠ 0 := by
        constructor
        all_goals omega
      rcases hnz with ⟨hxnz, hynz, hznz, hxyznz⟩
      have hprodnz : x*y*z ≠ 0 := by {
        repeat rw [Nat.mul_ne_zero_iff]
        exact ⟨⟨hxnz, hynz⟩, hznz⟩
      }
      rcases h with ⟨hx, hy, hz⟩
      apply even_iff_two_dvd.mpr
      -- prove p not divide x + y + z
      have hxyz : ¬ p ∣ x + y + z := by {
        intro h
        exact hz ((Nat.dvd_add_iff_right ((Nat.dvd_add_iff_right hx).mp hy)).mpr h)
      }
      -- by cases on whether x.factorization p ≤ y.factorization p
      by_cases hle : x.factorization p ≤ y.factorization p
      -- use inequalities to show x.factorization p = y.factorization p
      have hm := calc
        y.factorization p ≤ (x*z*(x+y+z)).factorization p := by {
          have hnz : x*z*(x+y+z) ≠ 0 := mul_ne_zero_iff.mpr ⟨(mul_ne_zero_iff.mpr ⟨hxnz, hznz⟩), hxyznz⟩
          exact (Nat.factorization_le_iff_dvd hynz hnz).mpr h₅ p
        }
        _ = x.factorization p + z.factorization p + (x+y+z).factorization p := by {
          repeat rw [factorization_mul]
          simp
          · exact hxnz
          · exact hznz
          · exact Nat.mul_ne_zero hxnz hznz
          · exact hxyznz
        }
        _ = x.factorization p := by {rw [factorization_eq_zero_of_not_dvd hz, factorization_eq_zero_of_not_dvd hxyz];simp}
      have hm' : x.factorization p = y.factorization p := by exact Nat.le_antisymm hle hm

      -- and then (x*y*z*(x+y+z)).factorization p is even
      have hm'' :(x*y*z*(x+y+z)).factorization p = 2*x.factorization p:= by {
        repeat rw [factorization_mul]
        simp
        rw [factorization_eq_zero_of_not_dvd hz, factorization_eq_zero_of_not_dvd hxyz, ← hm']
        ring
        · exact hxnz
        · exact hynz
        · exact Nat.mul_ne_zero hxnz hynz
        · exact hznz
        · exact hprodnz
        · exact hxyznz
      }
      omega
      · simp at hle
        have hm := calc
          x.factorization p ≤ (y*z*(x+y+z)).factorization p := by {
            have hnz : y*z*(x+y+z) ≠ 0 := mul_ne_zero_iff.mpr ⟨(mul_ne_zero_iff.mpr ⟨hynz, hznz⟩), hxyznz⟩
            exact (Nat.factorization_le_iff_dvd hxnz hnz).mpr h₄ p
          }
          _ = y.factorization p + z.factorization p + (x+y+z).factorization p := by {
            repeat rw [factorization_mul]
            simp
            · exact hynz
            · exact hznz
            · exact Nat.mul_ne_zero hynz hznz
            · exact hxyznz
          }
          _ = y.factorization p := by {rw [factorization_eq_zero_of_not_dvd hz, factorization_eq_zero_of_not_dvd hxyz];simp}
        exfalso
        linarith
    }

    -- case 3: p divides all of x, y, z
    have hc3 (h: (p ∣ x)∧( p ∣ y)∧(p ∣ z)) : Even ((x*y*z*(x+y+z)).factorization p) := by {
      rcases h with ⟨hx, hy, hz⟩
      have h := Nat.dvd_gcd (Nat.dvd_gcd hx hy) hz
      rw [h₃] at h
      exfalso
      exact hp.not_dvd_one h
    }

    -- considering different cases on whether p ∣ x, p ∣ y, p ∣ z
    by_cases hxdvd : p ∣ x
    all_goals by_cases hydvd : p ∣ y
    all_goals by_cases hzdvd : p ∣ z

    -- solve by applying corresponding pre-proven theorems
    -- case 1: p ∣ x, p ∣ y, p ∣ z
    · exact hc3 ⟨hxdvd, hydvd, hzdvd⟩

    -- case 2: p ∣ x, p ∣ y, ¬ p ∣ z
    · exact hc2 x y z h₀ h₁ h₂ h₃ h₄ h₅ h₆ h₇ ⟨hxdvd, hydvd, hzdvd⟩

    -- case 3: p ∣ x, ¬ p ∣ y, p ∣ z
    · let x' := x
      let y' := z
      let z' := y
      have hp₁ : x' + y' + z' = x + y + z := by ring
      have hp₂ : x' * y' * z' = x * y * z := by ring
      have h₀' : 0 < x' := h₀
      have h₁' : 0 < y' := h₂
      have h₂' : 0 < z' := h₁
      have h₃' : (x'.gcd y').gcd z' = 1 := by {
        rw [← h₃, Nat.gcd_assoc, Nat.gcd_comm z y, Nat.gcd_assoc]
      }
      have h₄' : x' ∣ y' * z' * (x' + y' + z') := by {
        rw [(show y' * z' * (x' + y' + z') = y*z*(x+y+z) from by ring)]
        exact h₄
        }
      have h₅' : y' ∣ x' * z' * (x' + y' + z') := by {
        rw [(show x' * z' * (x' + y' + z') = x*y*(x+y+z) from by ring)]
        exact h₆
        }
      have h₆' : z' ∣ x' * y' * (x' + y' + z') := by {
        rw [(show x' * y' * (x' + y' + z') = x*z*(x+y+z) from by ring)]
        exact h₅
        }
      have h₇' : x' + y' + z' ∣ x' * y' * z' := by rwa [hp₁, hp₂]
      have hmid := hc2 x' y' z' h₀' h₁' h₂' h₃' h₄' h₅' h₆' h₇' ⟨hxdvd, hzdvd, hydvd⟩
      rw [hp₁, hp₂] at hmid
      exact hmid

    -- case 4: p ∣ x, ¬ p ∣ y, ¬ p ∣ z
    · exact hc1 x y z h₀ h₁ h₂ h₃ h₄ h₅ h₆ h₇ ⟨hxdvd, hydvd, hzdvd⟩

    -- case 5: ¬ p ∣ x, p ∣ y, p ∣ z
    · let x' := z
      let y' := y
      let z' := x
      have hp₁ : x' + y' + z' = x + y + z := by ring
      have hp₂ : x' * y' * z' = x * y * z := by ring
      have h₀' : 0 < x' := h₂
      have h₁' : 0 < y' := h₁
      have h₂' : 0 < z' := h₀
      have h₃' : (x'.gcd y').gcd z' = 1 := by {
        rw [← h₃, gcd_comm, Nat.gcd_comm z y, gcd_assoc]
      }
      have h₄' : x' ∣ y' * z' * (x' + y' + z') := by {
        rw [(show y' * z' * (x' + y' + z') = x*y*(x+y+z) from by ring)]
        exact h₆
        }
      have h₅' : y' ∣ x' * z' * (x' + y' + z') := by {
        rw [(show x' * z' * (x' + y' + z') = x*z*(x+y+z) from by ring)]
        exact h₅
        }
      have h₆' : z' ∣ x' * y' * (x' + y' + z') := by {
        rw [(show x' * y' * (x' + y' + z') = y*z*(x+y+z) from by ring)]
        exact h₄
        }
      have h₇' : x' + y' + z' ∣ x' * y' * z' := by rwa [hp₁, hp₂]
      have hmid := hc2 x' y' z' h₀' h₁' h₂' h₃' h₄' h₅' h₆' h₇' ⟨hzdvd, hydvd, hxdvd⟩
      rw [hp₁, hp₂] at hmid
      exact hmid

    -- case 6: ¬ p ∣ x, p ∣ y, ¬ p ∣ z
    · let x' := y
      let y' := x
      let z' := z
      have hp₁ : x' + y' + z' = x + y + z := by ring
      have hp₂ : x' * y' * z' = x * y * z := by ring
      have h₀' : 0 < x' := h₁
      have h₁' : 0 < y' := h₀
      have h₂' : 0 < z' := h₂
      have h₃' : (x'.gcd y').gcd z' = 1 := by {
        rw [← h₃, Nat.gcd_comm y x]
      }
      have h₄' : x' ∣ y' * z' * (x' + y' + z') := by {
        rw [(show y' * z' * (x' + y' + z') = x*z*(x+y+z) from by ring)]
        exact h₅
        }
      have h₅' : y' ∣ x' * z' * (x' + y' + z') := by {
        rw [(show x' * z' * (x' + y' + z') = y*z*(x+y+z) from by ring)]
        exact h₄
        }
      have h₆' : z' ∣ x' * y' * (x' + y' + z') := by {
        rw [(show x' * y' * (x' + y' + z') = x*y*(x+y+z) from by ring)]
        exact h₆
        }
      have h₇' : x' + y' + z' ∣ x' * y' * z' := by rwa [hp₁, hp₂]
      have hmid := hc1 x' y' z' h₀' h₁' h₂' h₃' h₄' h₅' h₆' h₇' ⟨hydvd, hxdvd, hzdvd⟩
      rw [hp₁, hp₂] at hmid
      exact hmid

    -- case 7: ¬ p ∣ x, ¬ p ∣ y, p ∣ z
    · let x' := z
      let y' := y
      let z' := x
      have hp₁ : x' + y' + z' = x + y + z := by ring
      have hp₂ : x' * y' * z' = x * y * z := by ring
      have h₀' : 0 < x' := h₂
      have h₁' : 0 < y' := h₁
      have h₂' : 0 < z' := h₀
      have h₃' : (x'.gcd y').gcd z' = 1 := by {
        rw [← h₃, Nat.gcd_comm, Nat.gcd_comm z y, Nat.gcd_assoc]
      }
      have h₄' : x' ∣ y' * z' * (x' + y' + z') := by {
        rw [(show y' * z' * (x' + y' + z') = x*y*(x+y+z) from by ring)]
        exact h₆
        }
      have h₅' : y' ∣ x' * z' * (x' + y' + z') := by {
        rw [(show x' * z' * (x' + y' + z') = x*z*(x+y+z) from by ring)]
        exact h₅
        }
      have h₆' : z' ∣ x' * y' * (x' + y' + z') := by {
        rw [(show x' * y' * (x' + y' + z') = y*z*(x+y+z) from by ring)]
        exact h₄
        }
      have h₇' : x' + y' + z' ∣ x' * y' * z' := by rwa [hp₁, hp₂]
      have hmid := hc1 x' y' z' h₀' h₁' h₂' h₃' h₄' h₅' h₆' h₇' ⟨hzdvd, hydvd, hxdvd⟩
      rw [hp₁, hp₂] at hmid
      exact hmid

    -- case 8: ¬ p ∣ x, ¬ p ∣ y, ¬ p ∣ z
    · exact hc0 ⟨hxdvd, hydvd, hzdvd⟩
  }
