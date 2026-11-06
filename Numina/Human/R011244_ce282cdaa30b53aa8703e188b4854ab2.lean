import Mathlib
import Aesop

/-In order to complete a large job, 1000 workers were hired, just enough to complete the job on schedule. All the workers stayed on the job while the first quarter of the work was done, so the first quarter of the work was completed on schedule. Then 100 workers were laid off, so the second quarter of the work was completed behind schedule. Then an additional 100 workers were laid off, so the third quarter of the work was completed still further behind schedule. Given that all workers work at the same rate, what is the minimum number of additional workers, beyond the 800 workers still on the job at the end of the third quarter, that must be hired after three-quarters of the work has been completed so that the entire project can be completed on schedule or before?-/

theorem AIME_Algebra_724 (fstqt sndqt trdqt: ℚ) (hfst:fstqt=1/4) (hsnd:sndqt=(1000/4)/(900))(htrd:trdqt=((1000/4)/(800)))(m:ℕ):(fstqt+sndqt+trdqt+(1000/4)/((800+m))≤1)↔766≤m:= by
--We assume that each worker has constant rate 1 and the scheduled time is one in total, let fstqt,sndqt and trdqt be the time used in the first three quaters and m be the number of additional hired workers. We prove that this project can be completed on schedule if and only if 766≤m
  constructor
--We prove that we need to hire at least 766 workers
--hm is satisfied means the project is completed on schedule.
  · intro hm
--Substitute the time used in the first three
    rw[hfst,hsnd,htrd] at hm
--We simplify this condition hm
    field_simp at hm
    apply (div_le_one (by linarith)).mp at hm;ring_nf at hm
    contrapose! hm
--We need to use that Nat is discrete to deduce that m<766 means m≤765
    apply Nat.le_of_lt_succ at hm
    replace hm:(m:ℚ)≤765:=by simp only [Nat.cast_le_ofNat, hm]
    linarith
--We prove that if 766≤ m,  then this project can be completed, which means the time spend in total is not greater than 1.
  · intro hm
--Again we substitute the condition and simplify it.
    rw[hfst,hsnd,htrd];field_simp
    apply (div_le_one _).mpr;ring_nf
    replace hm:766≤(m:ℚ):=by simp_all [Nat.ofNat_le_cast]
    linarith;linarith