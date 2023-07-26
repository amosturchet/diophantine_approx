/-
In this file we will prove Liouville's Theorem in the usual form for irrational α in ℝ.
We will follow Zannier's "Lecture Notes on Diophantine Analysis" where the Liouville's Theorem is Theorem 2.3
-/
import field_theory.minpoly.is_integrally_closed
import data.real.irrational
import analysis.calculus.cont_diff
import data.polynomial.denoms_clearable
import algebra.gcd_monoid.finset
import algebra.gcd_monoid.basic
--import data.rat.defs
open_locale classical big_operators polynomial
open polynomial


--import data.polynomial
-- import analysis.calculus.mean_value
--MEAN VALUE THEOREM is
-- exists_has_deriv_at_eq_slope
-- LIOUVILLE IN MATHLIB
-- import number_theory.liouville.basic

-- import topology.algebra.ordered
-- EXTREME VALUE THEOREM (continuous function on compact obtains max)
-- is_compact.exists_forall_ge

noncomputable theory

-- notation `transcendental` x := ¬(is_algebraic ℤ x)


/- 
Servirebbe lemma che passa dal minpoly al polinomio in ℤ[X] primitivo di grado minimo che si annulla in x, per poter richimare il lemma qui sotto
 

Messaggio di Filippo:
 Io farei così: prima definisci una funzione
lean
def pippo : polynomial rat -> polynomial int :=

che prende un polinomio razionale e lo moltiplica per i coefficienti; mentre lo costruisci, ti scontri con la definizione di polinomio che è in docs#polynomial e che ti richiede per ogni `n : nat` un elemento di `int`; tu gli dai il coefficiente del polinomio razionale moltiplicato per il mcm, e poi applichi 
docs#rat.denom_eq_one_iff.

serve:


rat.denom_eq_one_iff


per lcm: guardare polynomial.integral_normalization

 -/

-- questo è circa int.exists_gcd_one'





lemma mul_denom_eq_one_iff_denom_dvd_fact (n :ℕ  ) (hn: n≠ 0)  (x :ℚ )  : (↑ n * x ).denom=1 ↔  ↑x.denom ∣ n :=
begin
  rw [rat.mul_num_denom , rat.coe_nat_denom , rat.coe_nat_num, one_mul],
  have hd: 0< (n:ℤ).gcd (x.denom :ℤ )   , {    
    exact  (nat.gcd_pos_of_pos_right) n x.pos,
  },
  rcases int.exists_gcd_one hd with ⟨ wn, wd, hcopw, hwn, hwd⟩ , 
  rw mul_comm,
  nth_rewrite 0 hwn,
  nth_rewrite 1 hwd,
  rw <-mul_assoc,
  rw rat.div_mk_div_cancel_left , 
  swap,  {
  apply norm_num.ne_zero_of_pos, 
  norm_cast,
  exact hd,
  },
  have hwdpos: 0<wd,{
    apply  pos_of_mul_pos_left (eq.trans_gt hwd ( nat.cast_pos.2 x.pos))  (le_of_lt (nat.cast_pos.2 hd)),
  },
  have h1: (rat.mk (x.num * wn) wd.nat_abs).denom = wd.nat_abs,{
    rw  <-rat.num_denom',{
      apply int.nat_abs_pos_of_ne_zero,
      apply norm_num.ne_zero_of_pos,
      exact  hwdpos,
    },
    rw int.nat_abs_mul,
    apply nat.coprime.mul;
    apply nat.coprime_iff_gcd_eq_one.2;
    rw <-int.gcd_eq_nat_abs,
    { 
      apply nat.eq_one_of_dvd_one,
      have hcopx : 1= x.num.gcd ↑(x.denom),{
        rw eq_comm,
        exact x.cop,
      },
      rw hcopx,
      apply gcd_dvd_gcd,
      refl,
      rw int.nat_abs_dvd_iff_dvd,
      exact dvd.intro _ (eq.symm hwd),
    },
    exact hcopw,
  },
  have h2 : ↑(wd.nat_abs)=wd,{
    norm_cast,
    exact abs_eq_self.2 (le_of_lt hwdpos),    
  },
  rw h2 at h1,
  rw h1,
  simp,
  split,{
    intro h,
    rw h at h2,
    rw <-h2 at hwd,
    simp at hwd,
    rw hwd,
    exact gcd_dvd_left _ _,
  },
  intro h,
  rw int.gcd_eq_right (has_dvd.dvd.nat_cast h) at hwd,
  simp at hwd,
  apply norm_num.nat_abs_pos,
  norm_cast,
  nth_rewrite 0 <-int.one_mul ↑(x.denom) at hwd,
  have : (x.denom : ℤ ) ≠  0,{
    exact norm_num.ne_zero_of_pos x.denom (nat.cast_pos.2 x.pos),
  },  
  apply is_domain.mul_right_cancel_of_ne_zero  (this),
  exact hwd,
end


def denom_coeffs (p : ℚ[X]): ℕ → ℕ := λ n,  (p.coeff n).denom

def lcm_denom_coeffs (p : ℚ[X]) : ℕ  := (p.support).lcm (denom_coeffs p)

def S: finset ℕ  :={0,1,2}
def f: ℕ →ℕ:= λ x, 4*x+4
#eval S.lcm f


theorem canc_denom_int (p : ℚ[X]) : ∀ n: ℕ , ↑(↑(lcm_denom_coeffs p) * (p.coeff n)).num=(↑(lcm_denom_coeffs p) * (p.coeff n)):=
begin
  intro n,
  rw <-rat.denom_eq_one_iff,
  by_cases n∈ p.support, {
    rw mul_denom_eq_one_iff_denom_dvd_fact,
    exact finset.dvd_lcm h,
    unfold lcm_denom_coeffs,
    intro h0,
    rw finset.lcm_eq_zero_iff at h0,
    have h1: ∃ m,  (p.coeff m).denom  = 0,{
      rw set.mem_def at h0,
      cases h0 with l hl,
      use l,
      exact hl.2,
    },
    cases h1 with m hm,
    apply norm_num.ne_zero_of_pos ((p.coeff m).denom :ℤ ),
    exact nat.cast_pos.2 (p.coeff m).pos,
    norm_cast,
    exact hm,
  },
  rw polynomial.not_mem_support_iff at h,
  rw h,
  simp,
end

/- theorem canc_denom_int (p : ℚ[X]) : ∀ n: ℕ , ↑(↑(lcm_denom_coeffs p) * (p.coeff n)).num=(↑(lcm_denom_coeffs p) * (p.coeff n)):=
begin
  intro n,
  rw <-rat.denom_eq_one_iff,
  by_cases p.coeff n=0,{
    rw h,
    simp,
  },
  rw mul_denom_eq_one_iff_denom_dvd_fact,
  rw <-ne.def  at h,
  --unfold lcm_denom_coeffs,
  {
    apply finset.dvd_lcm,
    rw polynomial.mem_support_iff ,
    exact h,
  },
  unfold lcm_denom_coeffs,
  intro h1,
  rw <-finset.lcm_eq_zero_iff at h,
    sorry,
end -/


def canc_denom2  (p : ℚ[X]) : ℚ[X] := (lcm_denom_coeffs p) • p 

def canc_denom (p : ℚ[X]) : ℚ[X] := 
∑ i in p.support,  monomial i  (↑(lcm_denom_coeffs p) * (p.coeff i))


def canc_denom3 : ℚ[X]→ ℤ [X]:= λ p,  ∑ i in p.support,  monomial i  (↑(lcm_denom_coeffs p) * (p.coeff i)).num

def canc_denom4 (p:ℚ [X]): ℤ [X]:=  ∑ i in p.support,  monomial i  (↑(lcm_denom_coeffs p) * (p.coeff i)).num

def poly_int_to_rat (q: ℤ[X]):ℚ [X]:= ∑ i in q.support,  monomial i ↑(q.coeff i) 

--sono bloccato col teorema sotto

theorem same_roots : ∀ p:ℚ[X], ∀ x:ℝ, polynomial.eval₂ (algebra_map ℚ ℝ) (x) p =0 ↔  polynomial.eval₂ (algebra_map ℚ  ℝ) (x) (poly_int_to_rat(canc_denom4 p))=0:=
begin
  
  intros p x,
  rw canc_denom4,
  
  rw poly_int_to_rat,
  
  
  nth_rewrite 1 polynomial.eval₂_eq_sum,
  rw polynomial.sum_def,
  sorry,
  
  rw polynomial.eval₂_eq_sum,
  simp,
  
  rw polynomial.sum_def,

  rw poly_int_to_rat,
  rw canc_denom4,
 -- rw polynomial.eval₂_add ,
  rw canc_denom_int,


  rw polynomial.eval₂_eq_sum,
  rw polynomial.eval₂_eq_sum,
  simp,
  
  rw canc_denom_int p _,
  split,{
    intro h,
    --simp,
    rw [polynomial.eval₂_eq_sum , polynomial.sum_def],
    simp,
    --rw canc_denom3,
    sorry,
  },
end


/- theorem same_roots : ∀ p:ℚ[X], ∀ x:ℝ, polynomial.eval₂ (algebra_map ℚ ℝ) (x) p =0 ↔  polynomial.eval₂ (algebra_map ℚ  ℝ) (x) (poly_int_to_rat(canc_denom4 p))=0:=
begin
  intros p x,
  rw polynomial.eval₂_eq_sum,
  rw polynomial.eval₂_eq_sum,
  simp,

  rw poly_int_to_rat,
  rw canc_denom4,
 -- rw polynomial.eval₂_add ,
  rw canc_denom_int,


  rw polynomial.eval₂_eq_sum,
  rw polynomial.eval₂_eq_sum,
  simp,
  
  rw canc_denom_int p _,
  split,{
    intro h,
    --simp,
    rw [polynomial.eval₂_eq_sum , polynomial.sum_def],
    simp,
    --rw canc_denom3,
    sorry,
  },
end -/

-- def to_subring
/- 
def pol: ℚ [X]:= 
X^2+ (1/2)* X +1/3

example : lcm_denom_coeffs pol = 6 :=
begin
  unfold lcm_denom_coeffs,
  have h1 : (pol).support= { 0,1,2},{
    rw finset.ext_iff,
    intro a,
    split,{
      --rw pol,
      intro ha,
      by_cases a<3,{
        sorry,
      },
      rw not_lt at h,
      exfalso,
      rw pol at ha,
      sorry,
    },
    --rw finsupp.mem_support_iff,
    sorry,
  },
  rw h1,
  rw pol,
  sorry,
end

 -/
/- 

Scusate per il casino, ho fatto esperimenti che non vorrei cancellare


def pol: ℚ [X]:=
X^2+ (1/2)* X +1/3

open set

example : lcm_denom_coeffs pol = 6 :=
begin
  unfold lcm_denom_coeffs,
  have h1 : (pol).support= { 0,1,2},{
    rw finset.ext_iff,
    intro a,
    split,{
      --rw pol,
      intro ha,
      by_cases a<3,{
        sorry,
      },
      rw not_lt at h,
      exfalso,
      rw pol at ha,
      sorry,
    },
    --rw finsupp.mem_support_iff,
    sorry,
  },
  rw h1,
  rw pol,
  sorry,
end

#eval gcd (6:ℤ)  (-9:ℤ )

example : (gcd (6:ℤ ) (9:ℤ ) )  = ↑ 3 :=
begin
  have h1 : 3 ∣ 6, use 2, ring,
  have h2 : 3 ∣ 9, use 3, ring,
  have h3 : ∀ c:ℤ  , c∣ 6→ c∣ 9→c∣ 3,{
    intros c hc1 hc2,
    cases hc1 with a ha,
    cases hc2 with b hb,
    use b-a,
    calc 3=9-6 : by ring
      ... = c * b-6 : by rw hb
      ... = c*b- c* a : by rw ha
      ... = c*(b-a) : by linarith,
  },
  apply associa
  --dvd_gcd_iff
end


 -/



 

/-
 The Lemma gives a lower bound on the absolute value of a polynomial f with integral coefficients evaluated at a rational number x which is not a root of f 
 -/
lemma poly_not_zero_low_bound (a b : ℤ  ) (p : ℤ [X]) (hb : 0<b ) 
(hpab : polynomial.aeval (  (a: ℚ ) / (b  : ℚ  ) ) (polynomial.map (algebra_map ℤ ℚ ) p )≠ 0) :1 ≤ (↑b)^(p.nat_degree)* abs( polynomial.aeval (  (a: ℚ ) / (b  : ℚ  ) ) (polynomial.map (algebra_map ℤ ℚ ) p ))  :=
begin
  exact one_le_pow_mul_abs_eval_div hb hpab,
end

/-
lemma: minimal polynomial of an irrational does not have rational roots
-/
lemma rat_not_root_minpoly_irrat (y : ℚ) (x : ℝ) (hirr : irrational x) (hint: is_integral ℚ x): ¬ (polynomial.is_root (minpoly ℚ x) y):=
begin
  by_contradiction,
  -- minimal polynomial is prime
  have h_prime := minpoly.prime hint,
  -- irreducible polynomial with a root has degree 1
  have h_irr_one := polynomial.degree_eq_one_of_irreducible_of_root (h_prime.irreducible) h,
  -- x is a root of its minimal polynomial
  have h_x_root :=  minpoly.aeval ℚ x,
  -- if x is a root of a degree one polynomial with ℚ coefficients then x ∈ ℚ 
  have h_x_Q := minpoly.mem_range_of_degree_eq_one ℚ x h_irr_one,
  -- Lean is able to figure out the contraddicition using hirr
  tauto,
end

def const_Liouville {x : ℝ} (hint : is_integral ℚ x) : ℝ := 
  sorry

variables {x : ℝ} (hint: is_integral ℚ x) 

lemma const_Liouville_pos : const_Liouville (hint) > 0 :=
  sorry

-- Liouville Theorem
include hint
-- add the hint in the hypothesis using the fact that is included in ``variables'' above
theorem liouville (hirr : irrational x) :   ∀ a b : ℤ, b > 0 → abs(x - (a / b)) > (1 / b^(minpoly ℚ x).nat_degree) :=
begin
-- exact zero_lt_one
intros a b hb,
-- mai UNFOLD definition
-- usare aeval di solito invece che eval₂
-- p is minpoly 
unfold is_integral at hint,
rcases hint with ⟨p, hpmonic, hpzero⟩,
-- richimare lemma che "trasforma" p a coeff in ℤ di grado minimo
-- richimare lemma che "trasforma" p a coeff in ℤ di grado minimo
-- cases hp with hpmonic hpzero,
have h1 : abs((polynomial.eval₂ (algebra_map ℚ ℝ) x p) - (polynomial.eval₂ (algebra_map ℚ ℝ) (↑ a / ↑ b) p)) = abs(polynomial.eval₂ (algebra_map ℚ ℝ) (↑ a / ↑ b) p),
-- the absolute values are the same since x is a zero of its minimal polynomial
{
    -- have := minpoly.aeval ℚ x,
    rw hpzero,
    simp,
},

have hmeanval : ∃ α : ℝ,  (α < x ) ∧ ( α > (↑a / ↑b ) ) ∧ abs((polynomial.eval₂ (algebra_map ℚ ℝ) x p) - (polynomial.eval₂ (algebra_map ℚ ℝ) (↑ a / ↑ b) p)) = abs (x - (↑ a / ↑ b )) * abs (polynomial.eval₂ (algebra_map ℚ ℝ) α (polynomial.derivative p)),
{
  sorry,
},

sorry,
end



