import Mathlib

/-To prove that the product of two quadratic residues is a quadratic residue, the product of a quadratic residue and a non-residue is a non-residue, and the product of two non-residues is a quadratic residue.-/
theorem my_favorite_theorem {p : ℕ} (hp : Nat.Prime p) :
  (∀ a b : ZMod p, IsSquare a → IsSquare b → IsSquare (a*b)) ∧
  (∀ (a b : ZMod p) (h:a≠0), IsSquare a → ¬IsSquare b → ¬IsSquare (a*b)) ∧
  (∀ a b : ZMod p, ¬IsSquare a → ¬IsSquare b → IsSquare (a*b)) := by 
  have hp_fact : Fact (Nat.Prime p) := ⟨hp⟩
  haveI := hp_fact
  haveI : NeZero p:= NeZero.of_gt'
  
  -- Part 1: Prove that the product of two squares is a square
  have p1:∀ a b : ZMod p, IsSquare a → IsSquare b → IsSquare (a*b):= by
    intro a b ha hb
    exact IsSquare.mul ha hb
    
  -- Part 2: Prove that if a is a non-zero square and b is not, then a*b is not a square
  have p2:∀ (a b : ZMod p) (h_ne:a≠0), IsSquare a → ¬IsSquare b → ¬IsSquare (a*b):= by
    intro a b h ha hb
    by_contra w
    obtain⟨r,hr⟩:=ha
    obtain⟨s,hs⟩:=w
    let r_inv:=r⁻¹
    let rb:=s*r_inv
    
    -- Proving that r⁻¹*r = 1 (r is invertible)
    have h1:r_inv*r=1:= by 
      refine ZMod.inv_mul_of_unit r ?_
      refine Ne.isUnit ?_
      by_contra w
      exact h (by simp[hr,w])
      
    -- Proving that (s*r_inv)² = b
    have h3:(s*r_inv)*(s*r_inv)=b:=by
      calc 
        (s*r_inv)*(s*r_inv) = s*s*r_inv*r_inv := by ring
        _= r*r*b*r_inv*r_inv := by rw [← hs,hr]
        _= b*(r_inv*r)^2 := by ring
        _= b*1^2 := by rw [← h1]
        _= b := by ring
        
    -- Deriving contradiction: b is a square
    have h5:IsSquare b :=by 
      exists (s*r_inv)
      simp[h3]
    exact hb h5
    
  -- Part 3: Prove that the product of two non-squares is a square
  have p3:∀ a b : ZMod p, ¬IsSquare a → ¬IsSquare b → IsSquare (a*b):= by
    intro a b ha hb
    -- Using Legendre symbol to characterize squares and non-squares
    have h1:legendreSym p a.val=-1:=by simp[legendreSym.eq_neg_one_iff,ha]
    have h2:legendreSym p b.val=-1:=by simp[legendreSym.eq_neg_one_iff,hb]
    have h3:legendreSym p (a.val*b.val)=1:=by
      rw[legendreSym.mul,h1,h2]
      simp
      
    -- Proving that a and b are not divisible by p
    have h4:¬p∣a.val:=by
      by_contra w
      have h5:a=0:=by 
        refine (ZMod.val_eq_zero a).mp ?_
        exact Nat.eq_zero_of_dvd_of_lt w (show a.val<p by apply ZMod.val_lt)
      have h6:IsSquare (0:ZMod p):=by exact isSquare_zero
      rw[← h5] at h6
      exact ha h6
      
    have h5:¬p∣b.val:=by
      by_contra w
      have h5:b=0:=by 
        refine (ZMod.val_eq_zero b).mp ?_
        exact Nat.eq_zero_of_dvd_of_lt w (show b.val<p by apply ZMod.val_lt)
      have h6:IsSquare (0:ZMod p):=by exact isSquare_zero
      rw[← h5] at h6
      exact hb h6
      
    -- Completing the proof using Legendre symbol properties
    let r:=a.val*b.val
    have h7:(r:ZMod p)≠0:= by 
      by_contra w
      exact (Nat.Prime.not_dvd_mul hp h4 h5) ((ZMod.natCast_zmod_eq_zero_iff_dvd r p).mp w)
    have h10: IsSquare ↑(r:ZMod p) := by
      exact (legendreSym.eq_one_iff' p h7).mp h3
    have h12: IsSquare ↑(a.val*b.val:ZMod p) := by
      rw[Nat.cast_mul a.val b.val] at h10
      exact h10
    simp at h12
    exact h12
  tauto