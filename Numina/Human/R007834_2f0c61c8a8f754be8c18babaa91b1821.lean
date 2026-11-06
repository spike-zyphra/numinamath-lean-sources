import Mathlib

/- For each positive integer $n$, the set of integers $\{0,1,\ldots,n-1\}$ is known as the $\textit{residue system modulo}$ $n$. Within the residue system modulo $2^4$, let $A$ be the sum of all invertible integers modulo $2^4$ and let $B$ be the sum all of non-invertible integers modulo $2^4$. What is $A-B$? -/
theorem number_theory_19379 :
    (∑ x in (ZMod.fintype (2^4)).elems.filter (fun x => IsUnit x) , x.val) -
    (∑ x in (ZMod.fintype (2^4)).elems.filter (fun x => ¬IsUnit x), x.val) = 8 := by

    -- for type convertion
    have type_convert (x: ℕ) : (@OfNat.ofNat (Fin 16) x Fin.instOfNat : Fin 16) = (x : ZMod 16) := by
        rfl

    -- unit of zmod 16 is the same as coprime with 16
    have unit_iff_gcd_eq_1 (x: ℕ): decide (IsUnit (x: ZMod 16)) = decide ((Nat.gcd x 16) = 1) := by
        simp
        let h1 := ZMod.isUnit_iff_coprime x 16
        simp at h1
        unfold Nat.Coprime at h1
        rw [<-h1]

    -- expand the sum
    unfold Fintype.elems ZMod.fintype
    simp
    unfold Fin.fintype
    unfold List.finRange


    -- turn `(List.range' 0 16)` into `[0, 1, ..., 16]`
    simp
    unfold Finset.filter
    simp

    -- check whether each number is coprime with 16, and sum them up
    -- this step need a lot of computation
    repeat (unfold List.filter; rw [type_convert, unit_iff_gcd_eq_1]; simp; try rw [type_convert, ZMod.val_natCast])
    simp
    native_decide
