import copy
import networkx as nx

def genmat_gate_cancellation(list_coef, CNOT_matrix, singleQ_matrix=None):
    '''
    Input the coefficients of each term of a Pauli String, generate matrix by optimizing the transition cost
    (gates) between Hamiltonians. It is a minimum-cost flow problem (MCFP).
    :param list_coef: list of floats
    :param CNOT_matrix: 2d matrix of floats of cnot gates
    :param singleQ_matrix: optional 2d matrix of floats of one-qubit gates.
        If omitted, a zero matrix with the same shape as CNOT_matrix is used.
    :return: A normalized transition matrix res where res[i][j] is the probability of transitioning
        from Pauli string i to j under the optimized gate cost model.
    '''
    # Calculate the total flow up to a scaling
    coef_scaled = [int(abs(x) * 10000 + 0.5) for x in list_coef]
    sum_hj_10 = sum(coef_scaled)
    nterm = len(coef_scaled)

    # Accept either an nterm x nterm matrix or a flat list with nterm*nterm entries.
    def _normalize_cost_matrix(matrix, name):
        if len(matrix) != nterm:
            if len(matrix) == nterm * nterm and all(not isinstance(v, (list, tuple)) for v in matrix):
                return [list(matrix[ii * nterm:(ii + 1) * nterm]) for ii in range(nterm)]
            raise ValueError(f"{name} must be {nterm}x{nterm} (or a flat list of length {nterm * nterm})")
        for row in matrix:
            if not isinstance(row, (list, tuple)) or len(row) != nterm:
                raise ValueError(f"{name} must be {nterm}x{nterm}")
        return matrix

    CNOT_matrix = _normalize_cost_matrix(CNOT_matrix, "CNOT_matrix")
    if singleQ_matrix is None:
        singleQ_matrix = [[0 for _ in range(nterm)] for _ in range(nterm)]
    else:
        singleQ_matrix = _normalize_cost_matrix(singleQ_matrix, "singleQ_matrix")

    G = nx.DiGraph()
    # Source point T and sink point T.
    G.add_node('s', demand=-int(sum_hj_10))
    G.add_node('t', demand=int(sum_hj_10))

    # Construct the two sides of the graph with all weight zero.
    for ii in range(nterm):
        G.add_edges_from([('s', (ii, 'b'), {"capacity": coef_scaled[ii], "weight": 0.0})])
        G.add_edges_from([((ii, 'c'), 't', {"capacity": coef_scaled[ii], "weight": 0.0})])

    # Construct the middle of the graph.
    for ii in range(nterm):
        for jj in range(nterm):
            if ii == jj:
                continue
            else:
                G.add_edges_from([((ii, 'b'), (jj, 'c'),
                {"capacity": coef_scaled[ii],
                 "weight": int(CNOT_matrix[ii][jj]) + int(singleQ_matrix[ii][jj])})])

    # Find the minimum cost flow in a directed graph
    # flowCost: This variable will store the cost of the minimum cost flow found in the graph G.
    # flowDict: This variable will store a dictionary representing the flow values on each edge of the graph
    # after the minimum cost flow has been computed.
    flowCost, flowDict = nx.network_simplex(G)

    flow_matrix = [[0.0 for i in range(nterm)] for j in range(nterm)]
    for head, info in flowDict.items():
        # Ignore the information of flow that start with s, t, (ii, 'c').
        if isinstance(head, tuple) == False:
            continue
        if head[1] != 'b':
            continue
        # Head info stands for the flow comes from which 'b' node, 
        # the tail info stands for the flow comes to which 'c' node.
        for tail, flow in info.items():
            flow_matrix[head[0]][tail[0]] = flow

    res = [[0.0 for i in range(nterm)] for j in range(nterm)]
    # normalization
    for ii in range(nterm):
        for jj in range(nterm):
            res[ii][jj] = float(flow_matrix[ii][jj]) / float(coef_scaled[ii])
    return res


if __name__ == '__main__':
    list_coef = [0.2, 0.5, 0.3]
    CNOT_matrix = [[0, 1, 3], [1, 0, 2], [2, 3, 0]]
    singleQ_matrix = [[0, 0, 0], [0, 0, 0], [0, 0, 0]]
    mat = genmat_gate_cancellation(list_coef, CNOT_matrix, singleQ_matrix)
    print("P_gc matrix:")
    for row in mat:
        print(" ".join(f"{val:.6f}" for val in row))
