import Mathlib

open Real
open scoped BigOperators

/- FRA   Determine all functions $f$ from the set of positive integers into the set of positive integers such that for all $x$ and $y$ there exists a non degenerated triangle with sides of lengths  $$ x, \quad f(y) \quad \text { and } \quad f(y+f(x)-1) . $$ -/
theorem number_theory_23899 (f : ℤ  → ℤ ) :
  (∀ x : ℤ , x > 0 →  f x > 0) ∧ ( ∀ x y : ℤ , x > 0 → y > 0 → (x + f y > f (y + f x - 1) ∧ f y + f (y + f x - 1) > x ∧ f (y + f x - 1) + x > f y) )
      ↔
      ∀ x : ℤ, x > 0 →  f x = x := by
      constructor

      --left to right: if conditions are satisfied, then f x = x.
      intro h
      obtain ⟨hfpos, htriInequ⟩ := h

      -- Step (1). f 1 = 1.
      have f1eq1 : f 1 = 1 := by
        -- f does not have an upper bound, by using the triangle inequalities
        have noUpperBound : ¬(∃ b : ℤ , b>0 ∧ ∀ x > 0, f x < b) := by
          intro ub
          obtain ⟨b, ⟨hbpos, hbupperBound⟩ ⟩ := ub

          have tbpos : 3*b > 0 := by linarith
          have ftbpos : f (3*b) >0 := by exact hfpos (3*b) tbpos
          have tbpftbm1pos : 3*b + f (3*b) -1 > 0 := by linarith
          have hf3bl : (f (3*b)) < b := by exact hbupperBound (3*b) tbpos
          have ftbpftbm1posleb : f (3*b + f (3*b) -1) < b := by exact hbupperBound (3*b + f (3*b) -1) tbpftbm1pos
          have hf3bu : (f (3*b)) > 2 * b := by
            have tempf3b : f (3*b) + f (3*b + f (3*b) -1) > 3*b := by apply (htriInequ (3*b) (3*b) tbpos tbpos).right.left
            calc
              f (3*b) > 3*b - f (3*b + f (3*b) -1) := by exact Int.sub_lt_iff.mpr tempf3b
              _ > 3*b - b := by linarith
              _ = 2 * b := by ring
          linarith

        --Prove that if f 1 ≠ 1, then f has a period (f 1 -1), so it has an upper bound.
        have f1ge1 : f 1 > 0:= by apply hfpos; exact Int.zero_lt_one;
        have f1g1false : ¬(f 1 > 1) := by
          intro f1g1
          have f1m1pos : f 1 -1 > 0 := by linarith

          have forallyfyeqfypf1m1: ∀ y:ℤ,  y>0 → f y = f (y + (f 1 -1)) := by
            intro y ypos
            have _: 1 + f y > f (y + f 1 -1) := by
              apply (htriInequ 1 y (gt_iff_lt.mpr Int.one_pos) ypos).left
            have _: f (y + f 1 -1) + 1 > f y := by
              apply (htriInequ 1 y (gt_iff_lt.mpr Int.one_pos) ypos).right.right

            have _: f y = f (y + f 1 -1) := by linarith
            have rew: y + f 1 - 1 = y + (f 1 - 1) := by ring
            rw [← rew]; assumption

          have forallyfyeqfyptf1m1 (y : ℤ )(hy : y >0) (t : ℕ) : f y = f (y + t * (f 1 -1)) := by
            induction' t with n hn
            ring_nf

            rw [hn]
            have ypnpos : y + n*(f 1 -1) > 0 := by
              apply Int.add_pos_of_pos_of_nonneg; linarith; apply Int.mul_nonneg; linarith; linarith;
            rw [forallyfyeqfypf1m1]
            simp; ring_nf; exact ypnpos

          have forallyfyeqzin0f1 : ∀ x : ℤ, (x >0) → ∃ y : ℤ, (y >0 ∧ y < f 1) ∧ f x = f y := by
            have forallxyf1divxmyfxeqfy (x y :ℤ) (hx : x> 0) (hy : y>0) (hxy: (f 1 - 1) ∣  x-y) : f x = f y := by
              have hyx : (f 1 - 1) ∣ y - x := by exact dvd_sub_comm.mp hxy
              by_cases xgy : y<x
              have exk : ∃k : ℕ, y+ k*(f 1 -1) = x := by
                use ((x-y)/(f 1 -1)).toNat
                have xmypos: 0<x-y := by linarith
                have zlf1m1: 0≤ f 1 -1 := by linarith
                have hpos: 0<(x-y)/(f 1-1) := by refine Int.ediv_pos_of_pos_of_dvd xmypos zlf1m1 hxy
                have noChange: ((x-y)/(f 1 -1)).toNat = (x-y) / (f 1 -1) := by  rw [Int.toNat_of_nonneg (by linarith)]
                rw [noChange];
                have  can: (x - y) / (f 1 - 1) * (f 1 - 1) = x-y := by exact Int.ediv_mul_cancel hxy
                rw [can]; ring
              obtain ⟨k, hk⟩ := exk
              have _: f y = f (y + ↑k * (f 1 - 1)) := by exact forallyfyeqfyptf1m1 y hy k
              rw [← hk]; symm; assumption

              by_cases xey : x = y
              rw [xey]

              have xley : x ≤ y := by exact Int.not_lt.mp xgy
              have xly : x<y := by exact lt_of_le_of_ne xley xey
              have exk : ∃k : ℕ, x +k*(f 1 -1) = y := by
                use ((y-x)/(f 1 -1)).toNat
                have xmypos: 0<y-x := by linarith
                have zlf1m1: 0≤ f 1 -1 := by linarith
                have hpos: 0<(y-x)/(f 1-1) := by refine Int.ediv_pos_of_pos_of_dvd xmypos zlf1m1 hyx
                have noChange: ((y-x)/(f 1 -1)).toNat = (y-x) / (f 1 -1) := by  rw [Int.toNat_of_nonneg (by linarith)]
                rw [noChange];
                have  can: (y - x) / (f 1 - 1) * (f 1 - 1) = y-x := by exact Int.ediv_mul_cancel hyx
                rw [can]; ring
              obtain ⟨k, hk⟩ := exk
              have _: f x = f (x + ↑k * (f 1 - 1)) := by exact forallyfyeqfyptf1m1 x hx k
              rw [← hk]; assumption



            have existsy (x : ℤ) (hx : x >0) : ∃ y : ℤ , (y >0 ∧ y< f 1) ∧ (f 1 - 1) ∣ x-y  := by
              by_cases f11divxmy : (f 1- 1) ∣ x
              use f 1 -1
              constructor; constructor; exact f1m1pos; linarith; exact dvd_sub_self_right.mpr f11divxmy

              use x % (f 1 -1)
              constructor; constructor;
              contrapose! f11divxmy
              have f1m1neq0 : (f 1 - 1) ≠ 0 := by linarith
              have xmodf1m1ge0 : 0 ≤ x % (f 1 -1) := by exact Int.emod_nonneg x f1m1neq0
              have xmodf1m1e0 : x % (f 1 -1 ) = 0 := by linarith
              rw [← Int.dvd_iff_emod_eq_zero] at xmodf1m1e0
              assumption
              have xmodf1m1lef1 : x % (f 1 -1) < f 1 - 1 := by exact Int.emod_lt_of_pos x f1m1pos
              linarith
              exact Int.dvd_sub_of_emod_eq rfl


            intro x hx
            obtain ⟨y, hy, hxy⟩ := existsy x hx
            use y

            constructor
            exact hy
            exact forallxyf1divxmyfxeqfy x y hx hy.left hxy


          have forallyin1mupperBound: ∃ b : ℤ, b>0 ∧ ∀ y : ℤ, (y>0 ∧  y <f 1)→ f y < b := by
            let S := Finset.Ioo 0 (f 1)
            have oneinS : 1 ∈ S := by
              rw [Finset.mem_Ioo]; simp; linarith
            have Snonemp : S.Nonempty := by use 1;

            use (S.image f).max' (Finset.Nonempty.image Snonemp f) + 1

            constructor
            -- it is > 0
            have h_max : f 1 ≤ (S.image f).max' (Finset.Nonempty.image Snonemp f) := by
              apply Finset.le_max'
              simp [Finset.mem_image]
              use 1;
            linarith

            -- indeed an upper bound
            intro y hy
            have hy' : y ∈ S := by simp [S, hy.1, hy.2]  -- y ∈ S because 0
            have h_le : f y ≤ (S.image f).max' (Finset.Nonempty.image Snonemp f) := by
              apply Finset.le_max'
              simp [Finset.mem_image, hy']
              use y
            linarith

          have upperBound : ∃ b : ℤ, b>0 ∧ ∀ x > 0, f x < b := by
            obtain ⟨b, hb⟩ := forallyin1mupperBound
            use b
            constructor
            exact hb.left

            intro x xpos
            have myy : ∃ y : ℤ, (y >0 ∧ y < f 1) ∧ f x = f y:= by
              apply forallyfyeqzin0f1 x xpos
            obtain ⟨y, hy⟩ := myy
            have _: f y < b := by exact hb.right y hy.left
            rw [hy.right]
            assumption

          contradiction

        linarith



      -- Step (2). f (f x) = x, by applying the triangle inequalities to x and 1.
      have ffxeq : ∀x : ℤ , x>0 → (f (f (x)) = x) := by
        intro x xpos
        have xp1gffx : x + f 1 > f (1+ f x -1) := by
          apply (htriInequ x 1 xpos (gt_iff_lt.mpr Int.one_pos)).left;
        have xp1lffx : f 1 + f (1+f x -1) > x := by
          apply (htriInequ x 1 xpos (gt_iff_lt.mpr Int.one_pos)).right.left;
        have xf1fxm1 : x = f (1 + f x -1) := by linarith
        have ffxeqf1fxm1 : f x = 1+ f x -1 := by ring
        rw [← ffxeqf1fxm1] at xf1fxm1; symm; exact xf1fxm1;




      -- Step 3. f x <= x.
      have fxlex (z : ℤ) (hz : z > 0) : (f (z)) ≤ z := by
        -- if there is such z
        by_contra hfz
        push_neg at hfz
        -- such z is at least 2
        have zge2 : z ≥ 2 := by
          have zneq1 : ¬ (z = 1) := by
            by_contra hz; rw [hz] at hfz; linarith
          omega

        have fzm1g1 : f z - 1 > 1 := by linarith
        have fzm1non0 : f z - 1 ≠ 0 := by linarith
        have zqg1 : (z : ℚ) > 1 := by norm_cast
        have fzqm1g1 : ((f z -1): ℚ ) > 1 := by norm_cast
        have zm1lfzm1 : z-1 < f z -1 := by linarith
        have zm1divfzm1pos : 0≤ (z-1 : ℚ)/ (f z -1 : ℚ) := by exact div_nonneg (by linarith) (by linarith)
        have zm1divfzm1l1 : (z-1 : ℚ)/(f z -1 : ℚ) < 1 := by rw [div_lt_one]; norm_cast; linarith;
        have zm1divfzm1squl1 : ((z - 1 : ℚ) / (f z - 1 : ℚ)) ^ 2 < 1:= by exact (sq_lt_one_iff₀ zm1divfzm1pos).mpr zm1divfzm1l1

        -- Let M = max {f 1, ... , f (f z -1)}. Then, there is
        -- no t such that f t > (z-1)/(f z -1) * t + M.
        let L := Finset.Icc 1 (f z -1)
        have Lnonemp : L.Nonempty := by
          use 1; rw [Finset.mem_Icc]; simp; linarith
        have oneinL : 1 ∈ L := by refine Finset.left_mem_Icc.mpr (by linarith)
        have f1infL : f 1 ∈ (L.image f) := by exact Finset.mem_image_of_mem f oneinL
        let M := (L.image f).max' (Finset.Nonempty.image Lnonemp f)
        have Mpos : M > 0 := by
          have _: f 1 ≤ M := by apply Finset.le_max'; exact f1infL
          linarith

        -- If there is such a t, we prove that (t - (f z -1)) still satisfies the assumption.
        have nosucht : ¬ (∃ t : ℤ, t >0  ∧   f t > (z-1 : ℚ)/ (f z -1 : ℚ)*t + M) := by
          intro ⟨t, ⟨tpos, ht⟩⟩
          let T := {x : ℤ | (0 < x ∧ x ≤ t)  ∧   f x > (z-1 : ℚ)/(f z -1 : ℚ )*x + M}
          have tinT : t ∈ T := by apply Set.mem_sep; constructor; linarith; exact Int.le_refl t; exact ht
          have Tnonempty: T.Nonempty := by use t
          have Tfin : T.Finite := by
            have Tsub: T ⊆ Finset.Icc 1 t := by
              intro x hx; simp; constructor; linarith [hx.left.left]; linarith [hx.left.right]
            exact Set.Finite.subset (Finset.finite_toSet (Finset.Icc 1 t)) Tsub
          have Thasmin: ∃ tmin ∈ T, ∀ t ∈ T, tmin ≤ t := by
            exact Set.exists_min_image T (fun a => a) Tfin Tnonempty
          obtain ⟨tmin, ⟨tmininT, htmin⟩⟩ := Thasmin
          have ftming: f tmin > ((z-1) : ℚ)/ ((f z -1): ℚ)*tmin + M := by simp [T] at tmininT; exact tmininT.right

          have tmfzm1lt : tmin - (f z -1) < tmin := by linarith

          have tmfzm1inT : (tmin - (f z -1)) ∈ T := by
            have tminpos : 0 < tmin := by simp [T] at tmininT; exact tmininT.left.left
            have oneletmin : 1 ≤ tmin := by linarith
            have tmingfzm1 : tmin > f z -1 := by
              have tminnotinL : tmin ∉ L := by
                have _: f tmin > M := by
                  have _: 0 < ((z-1) : ℚ)/ ((f z -1): ℚ)*tmin := by apply mul_pos; rw [div_pos_iff]; left; constructor; linarith; linarith; exact Rat.num_pos.mp tminpos
                  qify
                  calc
                    f tmin > ((z-1) : ℚ)/ ((f z -1): ℚ)*tmin + M := by exact ftming
                    _ > 0 + M := by gcongr
                    _ = M := by ring

                by_contra tmininL
                have _: f tmin ≤ M := by
                  have fmininImage: f tmin ∈ (Finset.image f L) := by exact Finset.mem_image_of_mem f tmininL
                  apply Finset.le_max';
                  exact fmininImage
                linarith
              simp [L] at tminnotinL; apply tminnotinL; assumption
            have tminmfzm1pos : 0 < (tmin - (f z - 1)) := by linarith
            have tminmfzm1let : (tmin - (f z -1)) ≤ t := by
              have _: tmin ≤ t := by exact htmin t tinT
              linarith
            have tmingood : (z-1 : ℚ) / (f z - 1 : ℚ) * (tmin - (f z -1)) + M < f (tmin - (f z -1)) := by
              --use the triangle inequality x = z and y = tmin - (f z -1)
              have _: z + f (tmin - (f z -1)) > f tmin := by
                calc
                  z + f (tmin - (f z -1)) > f (tmin - (f z -1) + f z -1) := by apply (htriInequ z (tmin - (f z -1)) (by linarith) (by linarith)).left
                  _ = f tmin := by ring_nf

              calc
                ↑ (f (tmin - (f z -1)))  ≥ ↑(f tmin - (z-1)) := by norm_cast; linarith
                _ > ((z-1 : ℚ) / ((f z - 1) : ℚ) * tmin + M - (z-1)) := by simp [ftming];
                _ = (z-1 : ℚ) / (f z - 1 : ℚ) * (tmin - (f z -1)) + M := by field_simp; ring

            simp [T]; constructor; constructor; linarith; linarith; assumption

          have tmletmfzm1 : tmin ≤ (tmin - (f z -1)) := by apply htmin (tmin - (f z -1)) tmfzm1inT
          linarith


        -- Let s be a sufficiently large integer. Using the inenquality in Lemma nosucht
        -- we prove that f (f s) < s, a contradiction to Step 2.
        push_neg at nosucht
        let s := Int.ceil (((z-1 : ℚ)/(f z -1 : ℚ) + 1) * M / (1 - ((z-1 : ℚ)/(f z -1 : ℚ))^2)) + 100
        have spos: s > 0 := by
          apply add_pos_of_nonneg_of_pos
          apply Int.ceil_nonneg
          apply div_nonneg;
          rw [mul_nonneg_iff_of_pos_right]; apply add_nonneg; assumption; linarith; exact Rat.num_pos.mp Mpos; linarith; linarith;
        have fspos : f s > 0 := hfpos s spos

        have ffsles : f (f s) < s := by
          have sbigtemp: (((z-1 : ℚ)/(f z -1 : ℚ) + 1) * M / (1 - ((z-1 : ℚ)/(f z -1 : ℚ))^2)) < s := by
            calc
              (((z-1 : ℚ)/(f z -1 : ℚ) + 1) * M / (1 - ((z-1 : ℚ)/(f z -1 : ℚ))^2)) ≤ Int.ceil (((z-1 : ℚ)/(f z -1 : ℚ) + 1) * M / (1 - ((z-1 : ℚ)/(f z -1 : ℚ))^2)) := by apply Int.le_ceil
              _ < s := by simp [s]
          have sbig :((z-1 : ℚ)/(f z -1 : ℚ))^2 * s + ((z-1 : ℚ)/(f z -1 : ℚ) + 1) * M < s := by
            have temppos: 0< (1 - ((z - 1 : ℚ) / (f z - 1 : ℚ)) ^ 2) := by linarith
            rw [div_lt_iff₀ temppos] at sbigtemp
            rw [mul_sub] at sbigtemp
            apply add_lt_of_lt_sub_left; linarith

          have fsles : f s ≤ ((z-1 : ℚ)/(f z -1 : ℚ) * s + M) := by apply nosucht s spos
          have fsslefa : f (f s) ≤ ((z-1 : ℚ)/(f z -1 : ℚ) * (f s) + M) := by apply nosucht (f s) fspos
          have tmp: f (f s) ≤ ((z-1 : ℚ)/(f z -1 : ℚ) * ((z-1 : ℚ)/(f z -1 : ℚ) * s + M) + M) := by nlinarith
          have eq : ((z-1 : ℚ)/(f z -1 : ℚ))^2 * s + ((z-1 : ℚ)/(f z -1 : ℚ) + 1) * M = ((z-1 : ℚ)/(f z -1 : ℚ) * ((z-1 : ℚ)/(f z -1 : ℚ) * s + M) + M) := by rw [pow_two]; ring
          rw [← eq] at tmp;
          have _: ((f (f s)):ℚ) < (s:ℚ) := by linarith
          qify; linarith


        rw [ffxeq s spos] at ffsles; linarith

      have xlefx : ∀x : ℤ , x>0 → x ≤  f x := by
        intro x xpos
        have fxpos : f x > 0 := by exact hfpos x xpos
        calc
          x = f (f (x)) := by symm; exact ffxeq x xpos
          _ ≤  f x := by apply fxlex (f x) fxpos
      have fxex : ∀ x : ℤ , x>0 →  f x = x := by
        intro x xpos
        exact le_antisymm (fxlex x xpos) (xlefx x xpos)
      exact fxex



      --right to left: f x = x satisfies the condition. Simple calculation.
      intro forxfxeqx
      constructor
      intro x hx
      calc
        f x = x := by apply forxfxeqx x hx
        _ > 0 := by exact hx
      intro x y xpos ypos

      have fxpos : f x >0 := by
        rw [forxfxeqx x xpos]
        exact xpos
      have fypos : f y >0 := by
        rw [forxfxeqx y ypos]
        exact ypos
      have ypfxm1pos : y + f x -1 >0 := by
        linarith

      constructor
      calc
        x + f y = x + y := by rw[forxfxeqx y ypos]
        _ = y + x := by ring
        _ > y + x -1 := by exact sub_one_lt (y + x)
        _ = y + f x - 1 := by rw[forxfxeqx x xpos]
        _ = f (y + f x -1) := by rw[forxfxeqx (y + f x -1) ypfxm1pos]
      constructor
      calc
        f y + f (y + f x - 1) = y + f (y + f x -1) := by rw[forxfxeqx y ypos]
        _ = y + (y + f x - 1) := by rw[forxfxeqx (y + f x -1) ypfxm1pos]
        _ = y + (y + x -1) := by rw[forxfxeqx x xpos]
        _ > x := by linarith
      calc
        f (y + f x -1) + x = y + f x -1 + x := by rw[forxfxeqx (y + f x -1) ypfxm1pos]
        _ = y + x -1 + x := by rw[forxfxeqx x xpos]
        _ > y := by linarith
        _ = f y := by rw[forxfxeqx y ypos]
