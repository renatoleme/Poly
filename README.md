# Poly

Methods for tableaux deductive system in Coq. With [Poly.v](Poly.v) you can implement different tableaux systems. In this repository, we have, currently, the following tableaux systems:

- [x] Classical Propositional Logic (CL)
- [x] Ecumenical Propositional Logic ($E_T$)

$E_T$ tableau system is implemented according to the description given in [1].

## Classical Propositional Logic (CL)

We define the set of propositions $L$ using only *nor* ($\downarrow$) as the primitive connective. 

$$
L ::= p \mid L \downarrow L
$$

Let $A,B \in L$ be two propositions. The two tableau rules we use for $A \downarrow B$ are the following.

$$
\frac{F A \downarrow B}{T A \mid T B}
$$

$$
\frac{T A \downarrow B}{F A ,  F B}
$$

The other connectives are then defined as follows (see [CL/CL1.v](CL/CL1.v)).

- $\neg A := A \downarrow A$
- $A \land B := (A \downarrow A) \downarrow (B \downarrow B)$
- $A \lor B := (A \downarrow B) \downarrow (A \downarrow B)$
- $A \to B := ((A \downarrow A) \downarrow B) \downarrow ((A \downarrow A) \downarrow B)$

# How to use

To run with default examples, open the root folder inside some terminal.  In the terminal, run:

```bash
chmod +x Run.sh
```

Then:

```bash
./Run.sh <logic> <implementation>
```

Where `<logic>` is one of the following:

- `CL`
- `ET`

and `<implementation>` is one of the following:

- `1`
- `2`
- etc.

Examples:

```bash
./Run.sh ET 1
```

Please look inside of each file for specific orientations about how to run with different examples.

## Requirements

- Coq 8.13.2 or later.

# References

1. LEME, Renato; CONIGLIO, Marcelo; LOPES, Bruno; VENTURI, Giorgio. Ecumenical Propositional Tableau. Studia Logica. 2023. *Forthcoming*.