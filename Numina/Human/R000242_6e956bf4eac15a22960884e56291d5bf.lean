import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat

/-Find with proof all positive  $3$  digit integers  $\overline{abc}$  satisfying 
\[ b\cdot \overline{ac}=c \cdot \overline{ab} +10 \]-/

theorem number_theory_8676 (a b c:Fin 10)(h:b.val*(10*a.val+c.val)=c.val*(10*a.val+b.val)+10):(let q:=100*a.val+10*b.val+c.val;q=110 ∨q=121 ∨q=132 ∨q=143 ∨q=154 ∨q=165 ∨q=176 ∨q=187 ∨q=198) :=by
  -- import the assumption
  intro q
  -- first, we need to prove a = 1
  -- simp at h
  ring_nf at h
  -- prove ab=ac+1
  conv at h=> rhs;rw[add_assoc,add_comm,add_assoc,add_comm]
  simp at h
  -- prove 10ab=10(ac+1)
  have h2:10*(a.val*b.val)=10*(a.val*c.val+1):= by ring_nf;ring_nf at h;linarith
  -- prove ab=ac+1
  simp at h2
  -- prove a=1,we need to prove a|1
  have ha:a.val ∣1:= by 
      --prove a|ac+1
      have hab: a.val∣ (a.val*c.val+1) := by rw [← h2];simp
      --prove a|ac
      have hac: a.val ∣ a.val * c.val := by simp
      --prove a|1
      exact (Nat.dvd_add_right hac).mp hab
  -- prove a=1
  simp at ha
  -- prove b=c+1
  rw [ha] at h2
  simp at h2
  -- now use b replace c at q
  have hq:q=100*a.val+10*b.val+c.val:= by simp
  rw [ha,h2]at hq
  simp at hq
  rw [hq]
  -- now conser all cases of c
  fin_cases c
  -- now repeatly decide
  native_decide
  native_decide
  native_decide
  native_decide
  native_decide
  native_decide
  native_decide
  native_decide
  native_decide
  -- for c=9, b can't be 10, contradicition
  simp at h2
  -- use contradiciton to prove
  apply False.elim
  omega
  
