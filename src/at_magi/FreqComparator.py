##
# @file
# Plot the solutions of a Tree
# On the left : create a tree with nodes having size corresponding to
#   the number of times they where taken
# On the right : a bar diagram of the number of time each node is taken
#
import networkx as nx
import matplotlib.pyplot as plt

def frequency_comparator(nodes, edges, current_network, current_digraph, sol_array, var_array):

    values = compute_values(nodes, current_network, current_digraph, sol_array, var_array)
    maximum = len(sol_array)

    node_max_size = 3000
    font_max_size = 15

    if len(values) > 20:
        factor = len(values) / 15
        factor = min(2, factor)
    else:
        factor = 1

    current_l = round(15 * factor)
    current_w = round(7 * factor)
    current_dpi = round(100 / factor)

    plt.ion()
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(current_l,current_w), dpi=current_dpi)

    g = nx.DiGraph()

    good_to_show = [i[0] for i in nodes if i[1]["type"] != "CtMs"]
    g.add_nodes_from(good_to_show)
    g.add_edges_from([i for i in edges if i[1] in good_to_show and i[0] in good_to_show])
    pos1 = nx.nx_agraph.graphviz_layout(g, prog='dot', args='')

    sizes = [(values[k]/maximum)*node_max_size for k in values]

    color_map = []
    for n in g:
        v = values[n]/maximum * 100
        if v > 80:
            color_map.append('red')
        elif v < 40:
            color_map.append('lime')
        else: 
            color_map.append('orange') 

    nx.draw(g, pos1, with_labels=False, arrows=True, node_size=sizes, ax=ax1, node_color=color_map)
    for node, (x, y) in pos1.items():
        ax1.text(x, y, node, fontsize=values[node]/maximum*font_max_size, ha='center', va='center')

    names = list(values.keys())
    values = list(values.values())
    ax2.bar(range(len(values)), values, tick_label=names)
    plt.gca().set(title='Frequency Histogram', ylabel='Frequency')
    plt.xticks(rotation=45, ha='right')
    
    fig.tight_layout()


def compute_values(nodes, current_network, current_digraph, sol_array, var_array):

    counter = {i[0]:0 for i in nodes if i[1]["type"] != "CtMs"}

    for index in range(len(sol_array)):
        values = {i[0]:False for i in nodes if i[1]["type"] != "CtMs"}
        
        values_logic = {i[0]:False for i in current_digraph.nodes(data=True) if i[0] not in values}

        ok_list = []
        not_list = []
        
        for i, v in enumerate(sol_array[index]) :
            if v == "True" :
                ok_list.append(var_array[i])
            else:
                not_list.append(var_array[i])

        path_count_set = {}

        cur_net_nodes_dict = {d['id']: d for d in current_network.nodes}
        cur_digraph_nodes_dict = dict(current_digraph.nodes(data=True))

        for n in current_network.nodes :
            if n['id'] in ok_list:
                values[n['id']] = True
                for e in current_network.edges :
                    if e['to'] == n['id']:
                        recur_path(e, path_count_set, True, cur_net_nodes_dict, cur_digraph_nodes_dict, current_network, values, values_logic)
            elif n['id'] in not_list:
                for e in current_network.edges :
                    if e['to'] == n['id']:
                        recur_path(e, path_count_set, False, cur_net_nodes_dict, cur_digraph_nodes_dict, current_network, values, values_logic)

        for key in values:
            if values[key] == True:
                counter[key] = counter[key] + 1

    return counter

def recur_path(current_edge, path_count_set, taken, cur_net_nodes_dict, cur_digraph_nodes_dict, current_network, values, values_logic):
        current = current_edge['from']
        n = cur_net_nodes_dict[current]
        d = cur_digraph_nodes_dict[current]
        
        next_taken = False
        if taken:
            if d['type'] == 'logic' or d['type'] == 'cmlogic' :
                if current in path_count_set :
                    path_count_set[current].add(current_edge['to'])
                else:
                    path_count_set[current] = {current_edge['to']}

                if d['inputNbr'] == -1 or d['inputNbr'] == len(path_count_set[current]):
                    next_taken = True
                    values_logic[n['id']] = True

                elif d['inputNbr'] == -3 :
                    if len(path_count_set[current]) % 2 != 0 :
                        next_taken = True
                        values_logic[n['id']] = True
                    else:
                        values_logic[n['id']] = False

                elif d['inputNbr'] == -2:
                    values_logic[n['id']] = False
            else :
                next_taken = True
                values[n['id']] = True
        else:
            if d['type'] == 'logic' or d['type'] == 'cmlogic' :
                if d['inputNbr'] == -2 :
                    next_taken = True
                    values_logic[n['id']] = not values_logic[n['id']]

                elif d['inputNbr'] == -3 :
                    if current in path_count_set:
                        if current_edge['to'] in path_count_set[current]:
                            path_count_set[current].remove(current_edge['to'])
                        if len(path_count_set[current]) % 2 != 0 :
                            next_taken = True
                            values_logic[n['id']] = True
                        else:
                            values_logic[n['id']] = False

                elif values_logic[n['id']] == True:
                    return
            else:
                values[n['id']] = False

        for e in current_network.edges :
            if e['to'] == n['id']:
                recur_path(e, path_count_set, next_taken, cur_net_nodes_dict, cur_digraph_nodes_dict, current_network, values, values_logic)

if __name__ == "__main__":
    frequency_comparator(None, None, None)