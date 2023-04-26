# AH

Data specification:

$$
\begin{align*}

\end{align*}
$$

Transition rules:
$$
\begin{align*}
\langle V^*, E, K \rangle &\longmapsto \langle K, V^* \rangle && \\
\langle x, \text{nil}, K \rangle &\longmapsto \langle \text{errcont}, x \rangle && \\
\langle x, ((y \cdot V) \cdot E), K \rangle &\longmapsto \langle \langle \text{lookup } y, V, E, K\rangle, x \rangle && \\ 
\langle \text{let } (x \, M) \, B, E, K \rangle &\longmapsto \langle M, E, \langle \text{letcont } x, B, E, K\rangle \rangle && \\
\langle \text{if } C \, M \, N, E, K \rangle &\longmapsto \langle C, E, \langle \text{ifcont } M, N, E, K\rangle \rangle && \\
\langle \text{quote} \, D, E, K \rangle &\longmapsto \langle K, D \rangle && \\
\langle \text{eval} \, M \, E', E, K \rangle &\longmapsto \langle M, E, \langle \text{evalcont} \, E', K  \rangle \rangle && \\
\langle F \, A_1 \ldots A_n, E, K \rangle &\longmapsto \langle F, E, \langle \text{ap } \text{nil}, (A_1, \ldots, A_2), E, K\rangle  \rangle && \\ \\

\langle \langle \text{lookup } y, V^*, E, K\rangle, x \rangle &\longmapsto \langle K, V^* \rangle && \text{where \(x = y\)} \\
&\longmapsto \langle x, E, K \rangle && \text{where \(x \neq y\)} \\
\langle \langle \text{letcont } x, B, E, K\rangle, V^* \rangle &\longmapsto \langle B, E[x := V^*], K \rangle \\
\langle \langle \text{ifcont } M, N, E, K\rangle, V^* \rangle &\longmapsto \langle M, E, K \rangle && \text{where \(V^* =\) nil} \\
&\longmapsto \langle N, E, K \rangle && \text{where \(V^* \neq\) nil} \\
\langle \langle \text{evalcont} \, E, K\rangle, V^* \rangle &\longmapsto \langle V^*, E, K \rangle && \\
\langle \langle \text{ap} \, (\ldots, V_i^*), (A_{i + 2}, \ldots), E, K\rangle, V_{i + 1}^* \rangle &\longmapsto \langle A_{i + 2}, E, \langle \text{ap} \, (\ldots, V_i, V_{i + 1}) \, (A_{i + 3}, \ldots), E, K \rangle \rangle && \\
\langle \langle \text{ap} \, (\ldots, V_{n - 1}^*), \text{nil}, E, K\rangle, V_{n}^* \rangle &\longmapsto \langle A_{i + 2}, E, \langle \text{ap} \, (\ldots, V_i, V_{i + 1}) \, (A_{i + 3}, \ldots), E, K \rangle \rangle && \\
\end{align*}
$$
 