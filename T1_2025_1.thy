theory T1_2025_1
  imports Main
begin

(*Alunos: Felipe R. Tasoniero, Lucas S. Wolschick*)

(*Exercicio 1*)
primrec pot :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
poteq1: "pot x 0 = Suc 0" |
poteq2: "pot x (Suc y) = x * pot x y"

lemma t1: "\<forall>x m::nat. pot x (m + n) = pot x m * pot x n"
proof (induction n)
  case 0
  show "\<forall>x m::nat. pot x (m + 0) = pot x m * pot x 0"
  proof (rule allI, rule allI)
    fix A :: nat and B :: nat
    have "pot A (B + 0) = pot A B" by simp
    also have "... = pot A B * 1" by simp
    also have "... = pot A B * pot A 0" by (simp only: poteq1)
    finally show "pot A (B + 0) = pot A B * pot A 0" .
  qed
next
  case (Suc n)
  show "\<forall>x m::nat. pot x (m + Suc n) = pot x m * pot x (Suc n)"
  (*Suc.IH: \<forall>x m. pot x (m + n) = pot x m * pot x n*)
  proof (rule allI, rule allI)
    fix A :: nat and B :: nat
    have "pot A (B + Suc n) = pot A (Suc (B + n))" by simp
    also have "... = A * pot A (B + n)" by (simp only: poteq2)
    also have "... = A * (pot A B * pot A n)" using Suc.IH by simp
    also have "... = (A * pot A n) * pot A B" by simp
    also have "... = pot A (Suc n) * pot A B" by (simp only: poteq2)
    also have "... = pot A B * pot A (Suc n)" by simp
    finally show "pot A (B + Suc n) = pot A B * pot A (Suc n)" .
  qed
qed

theorem t2: "\<forall>x m::nat. pot x (m * n) = pot (pot x m) n"
  proof (induction n)
  case 0
  show "\<forall>x m. pot x (m * 0) = pot (pot x m) 0"
  proof (rule allI, rule allI)
    fix x m :: nat
    have "pot x (m * 0) = pot x 0" by simp
    also have "... = 1" by (simp only: poteq1)
    also have "... = pot (pot x m) 0" by (simp only: poteq1)
    finally show "pot x (m * 0) = pot (pot x m) 0" .
  qed
next
  case (Suc n)
  show "\<forall>x m. pot x (m * Suc n) = pot (pot x m) (Suc n)"
  proof (rule allI, rule allI)
    fix x m :: nat
    have "pot x (m * Suc n) = pot x (m + (m * n) )" by simp
    also have "... = pot x (m * n) * pot x m" using t1 by simp
    also have "... = pot (pot x m) n * pot x m" using Suc.IH by simp
    also have "... = pot x m * pot (pot x m) n" by simp
    also have "... = pot (pot x m) (Suc n)" by (simp only: poteq2)
    finally show "pot x (m * Suc n) = pot (pot x m) (Suc n)" .
  qed
qed

(*Exercicio 2*)
primrec cat :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
cateq1: "cat [] ys = ys" |
cateq2: "cat (x#xs) ys = x#cat xs ys"

primrec reverso :: "'a list \<Rightarrow> 'a list" where
reveq1: "reverso [] = []" |
reveq2: "reverso (x#xs) = cat (reverso xs) [x]"

primrec somatorio :: "nat list \<Rightarrow> nat" where
somaeq1: "somatorio [] = 0" |
somaeq2: "somatorio (x#xs) = x + somatorio xs"

lemma t3: "\<forall>ys::nat list. somatorio (cat xs ys) = somatorio xs + somatorio ys"
proof (induction xs)
  case Nil
  show "\<forall>ys. somatorio (cat [] ys) = somatorio [] + somatorio ys"
  proof (rule allI)
    fix ys :: "nat list"
    have "somatorio (cat [] ys) = somatorio ys" by (simp only: cateq1)
    also have "... = 0 + somatorio ys" by simp
    also have "... = somatorio [] + somatorio ys" by (simp only: somaeq1)
    finally show "somatorio (cat [] ys) = somatorio [] + somatorio ys" .
  qed
next
  case (Cons x xs)
  show "\<forall>ys. somatorio (cat (x # xs) ys) = somatorio (x # xs) + somatorio ys"
  proof (rule allI)
    fix ys :: "nat list"
    have "somatorio (cat (x # xs) ys) = somatorio (x # cat xs ys)" by (simp only: cateq2)
    also have "... = x + somatorio (cat xs ys)" by (simp only: somaeq2)
    also have "... = x + (somatorio xs + somatorio ys)" using Cons.IH by simp
    also have "... = (x + somatorio xs) + somatorio ys" by simp
    also have "... = somatorio (x # xs) + somatorio ys" by (simp only: somaeq2)
    finally show "somatorio (cat (x # xs) ys) = somatorio (x # xs) + somatorio ys" .
  qed
qed

theorem t4: "somatorio (reverso xs) = somatorio xs"
proof (induction xs)
  case Nil
  have "somatorio (reverso []) = somatorio []" by (simp only: reveq1)
  then show ?case by (simp only: somaeq1)
next
  case (Cons x xs)
  have "somatorio (reverso (x # xs)) = somatorio (cat (reverso xs) [x])"
    by (simp only: reveq2)
  also have "... = somatorio (reverso xs) + somatorio [x]"
    using t3 by simp
  also have "... = somatorio xs + somatorio [x]"
    using Cons.IH by simp
  also have "... = somatorio (x # xs)"
    by simp
  finally show ?case .
qed
end