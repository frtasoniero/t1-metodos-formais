# **Formal Methods – Project 1**

## 📝 **Project Theme**

> **Proofs by Induction of Recursive Equational Specifications**

## 🎯 **Objective**

> Build recursive equational specifications, perform formal proofs by induction, and verify them in the Isabelle system using the Isar language.

## 🧩 **Problems**

### 1. 🔢 **Recursive Function for Power Calculation**

#### **Specification**

```plaintext
pot: ℕ × ℕ → ℕ

pot(x, 0) = 1
pot(x, y + 1) = x * pot(x, y)
```

#### **Tasks**

* **Prove the Lemma:**

  > For all $x, m, n \in \mathbb{N}$:
  >
  > $$
  > \text{pot}(x, m + n) = \text{pot}(x, m) \times \text{pot}(x, n)
  > $$

* **Then, using the lemma, prove the Theorem:**

  > For all $x, m, n \in \mathbb{N}$:
  >
  > $$
  > \text{pot}(x, m \times n) = \text{pot}(\text{pot}(x, m), n)
  > $$

---

### 2. 📋 **Recursive Functions on Lists**

#### **Specifications**

* **Concatenation (`cat`):**

  ```plaintext
  cat: List(τ) × List(τ) → List(τ)
  cat([], ys) = ys
  cat(x:xs, ys) = x : cat(xs, ys)
  ```

* **Reverse (`reverso`):**

  ```plaintext
  reverso: List(τ) → List(τ)
  reverso([]) = []
  reverso(x:xs) = cat(reverso(xs), [x])
  ```

* **Sum (`somatorio`):**

  ```plaintext
  somatorio: List(τ) → ℕ
  somatorio([]) = 0
  somatorio(x:xs) = x + somatorio(xs)
  ```

#### **Tasks**

* **Prove the Lemma:**

  > For all $xs, ys \in \text{List}(\mathbb{N})$:
  >
  > $$
  > \text{somatorio}(\text{cat}(xs, ys)) = \text{somatorio}(xs) + \text{somatorio}(ys)
  > $$

* **Then, using the lemma, prove the Theorem:**

  > For all $xs \in \text{List}(\mathbb{N})$:
  >
  > $$
  > \text{somatorio}(\text{reverso}(xs)) = \text{somatorio}(xs)
  > $$

## 📦 **Submission Checklist**

* **Deliverables:**

  1. 📝 **PDF Document:**

     * Formal induction proofs in the classroom demonstration style
     * Name of all group members
  2. 💻 **Isabelle File (`.thy`):**

     * Complete Isabelle source code
     * Name of all group members

## 🗒️ Professor's Notes After Review

  - **Task 1**

     * **Manual proof (pdf)**: ok
     * **Automated proof**: ok

  - **Task 2**

     * **Manual proof (pdf)**: ok
     * **Automated proof**: ok

  - **Task 3**

     * **Manual proof (pdf)**: ok
     * **Automated proof**: ok

  - **Task 4**

     * **Manual proof (pdf)**: ok
     * **Automated proof**: skips proof steps at the end using `simp`
