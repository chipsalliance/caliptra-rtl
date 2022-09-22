import scipy.interpolate as spi
import numpy as np
import pandas as pd
import matplotlib.pyplot as plt
import csv
import os
from itertools import zip_longest
import pandas as pd


def get_equation(x, y, degree=1):
    coefs, res, _, _, _ = np.polyfit(x, y, degree, full=True)
    ffit = np.poly1d(coefs)
    print(ffit)
    return ffit


def tvla_plots(directory, predicted_point=1000000):
    file_name = os.path.join(directory, f'./data/tvla.csv')
    with open(file_name, 'r') as csvfile:
        plots = csv.reader(csvfile, delimiter=',', quoting=csv.QUOTE_NONNUMERIC)
        for row in plots:
            a = np.array(row)
            break

    trace_lenght = a.size - 1
    x = np.zeros(trace_lenght)

    with open(file_name, 'r') as csvfile:
        plots = csv.reader(csvfile, delimiter=',', quoting=csv.QUOTE_NONNUMERIC)
        cnt = 0
        count_45 = []
        count_x_axis = []
        for row in plots:
            x = np.array(row[:trace_lenght])
            result = x[x > 4.5]
            count_45.append(len(result))
            cnt += 1
            count_x_axis.append(cnt * 100)

        maxind = x.argmax(axis=0)

    result_path = os.path.join(directory, f'./attack/result')
    isExist = os.path.exists(result_path)
    if not isExist:
        os.makedirs(result_path)

    # for degree in [1, 2, 3, 4, 5, 6]:
    #     predict= get_equation(count_x_axis, count_45,degree)
    #     print(predict(10000000))

    predict = get_equation(count_x_axis, count_45)
    # np.arange(start, end + step, step)
    x_new = np.arange((cnt + 1) * 100, predicted_point + 100, 100)

    plt.plot(count_x_axis, count_45)
    plt.plot(predicted_point, predict(predicted_point), 'ro')
    plt.savefig(os.path.join(directory, f'./attack/result/num_failures.png'))
    plt.close()
    plt.plot(x)
    plt.savefig(os.path.join(directory, f'./attack/result/1st-order-tvla-{cnt * 100}-trace.png'))
    plt.close()
    if maxind > 1000:
        down = maxind - 1000
    else:
        down = maxind

    if maxind < (trace_lenght - 1000):
        up = maxind + 1000
    else:
        up = maxind

    with open(file_name, 'r') as csvfile:
        plots = csv.reader(csvfile, delimiter=',', quoting=csv.QUOTE_NONNUMERIC)
        max_t_values = []
        for row in plots:
            x = np.array(row[:trace_lenght])
            z = x[down: up]
            z_max = z.argmax(axis=0)
            print(z[z_max])
            max_t_values.append(z[z_max])

    predict = get_equation(count_x_axis, max_t_values)
    # np.arange(start, end + step, step)

    plt.plot(count_x_axis, max_t_values)
    # plt.plot(x_new, predict(x_new), 'ro')
    a = predict(predicted_point)
    plt.plot(predicted_point, predict(predicted_point), 'ro')
    plt.savefig(os.path.join(directory, f'./attack/result/1st-order-tvla-evolution.png'))
    plt.close()

    data = [count_x_axis, count_45, max_t_values]
    export_data = zip_longest(*data, fillvalue='')
    with open(os.path.join(directory, f'./attack/result/raw_data.csv'), 'w', encoding="ISO-8859-1", newline='') as file:
        write = csv.writer(file)
        write.writerow(("# traces ", "# t > 4.5 t", "max"))
        write.writerows(export_data)


def CPA(directory, correct_key=0x7b689417, itr=0):
    row_number = 0
    for i in range(0, itr):
        file_name = os.path.join(directory, f'./data/powertrace_rnd_{i}.csv')
        with open(file_name, 'r') as csvfile:
            traces = csv.reader(csvfile, delimiter=',', quoting=csv.QUOTE_NONNUMERIC)
            for row in traces:
                a = np.array(row)
                row_number += 1

    trace_lenght = a.size - 1
    raw_traces = np.zeros((row_number, trace_lenght))

    cnt = 0
    for i in range(0, itr):
        file_name = os.path.join(directory, f'./data/powertrace_rnd_{i}.csv')
        with open(file_name, 'r') as csvfile:
            traces = csv.reader(csvfile, delimiter=',', quoting=csv.QUOTE_NONNUMERIC)
            for trace in traces:
                raw_traces[cnt] = np.array(trace[:trace_lenght])
                cnt += 1

    print("TRACES are READ...")
    file_name = os.path.join(directory, f'./MM_vector_spare.csv')
    raw_plaintext = np.zeros((row_number, 2), dtype=np.int64)

    with open(file_name, 'r') as csvfile:
        plaintexts = csv.reader(csvfile, delimiter=',', quoting=csv.QUOTE_NONNUMERIC)
        cnt = 0
        for plaintext in plaintexts:
            plaintext = [np.int64(item) for item in plaintext]
            p2 = ((plaintext[40] << 24) | (plaintext[41] << 16) | (plaintext[42] << 8) | (plaintext[43])) & 0xFFFFFFFF
            p1 = (((plaintext[44] & 0xFF) << 24) | ((plaintext[45] & 0xFF) << 16) | ((plaintext[46] & 0xFF) << 8) | (
                    plaintext[47] & 0xFF)) & 0xFFFFFFFF
            raw_plaintext[cnt] = [p1, p2]
            cnt += 1
            if cnt == row_number:
                break

    start_to_search = correct_key
    HD_matrix = np.zeros((row_number, 165), dtype=np.int64)
    HD_matrix2 = np.zeros((row_number, 165), dtype=np.int64)
    for i in range(0, row_number):
        for j in range(0, 165):
            key_guess = np.int64(((start_to_search >> (j & 0xF)) + j*43) & 0xFFFFFFFF)
            inter_1 = np.int64(raw_plaintext[i, 1] * key_guess)
            MSB_w = np.int64((inter_1 >> 32) & 0xFFFFFFFF)
            LSB_w = np.int64(inter_1 & 0xFFFFFFFF)
            inter_2 = np.int64(raw_plaintext[i, 0] * key_guess)
            MSB_w2 = np.int64((inter_2 >> 32) & 0xFFFFFFFF)
            # LSB_w2 = np.int64(inter_2 & 0xFFFFFFFF)
            # HD_matrix[i, j] = HW_calculator(inter_1 ^ inter_2) # + HW_calculator(LSB_w ^ LSB_w2)
            HD_matrix[i, j] =HW_calculator(LSB_w) + HW_calculator(inter_1)
            HD_matrix2[i, j] = HW_calculator(MSB_w ^ MSB_w2)

    a = np.mean(raw_traces, axis=0)
    var_realmeas = raw_traces - a
    pearson_array_result = np.zeros((165, trace_lenght))
    pearson_array_result2 = np.zeros((165, trace_lenght))
    std_traces = np.std(raw_traces, axis=0)
    for i in range(0, 165):
        res_array = HD_matrix[:, i]
        var_res = res_array - np.mean(res_array, axis=0)
        var_res = var_res.T
        num = np.matmul(var_res, var_realmeas)
        std_plaintext = np.std(res_array, axis=0)
        denum = std_plaintext * std_traces
        result = (num / row_number) / denum
        pearson_array_result[i] = result
        maxind = result.argmax(axis=0)
        minind = result.argmin(axis=0)
        print(f"iteration : {hex(np.int64(start_to_search + i*5793671) & 0xFFFFFFFF)}, max index={maxind} and value is {result[maxind]} min index={minind} "
              f"and value is {result[minind]}")
        res_array = HD_matrix2[:, i]
        var_res = res_array - np.mean(res_array, axis=0)
        var_res = var_res.T
        num = np.matmul(var_res, var_realmeas)
        std_plaintext = np.std(res_array, axis=0)
        denum = std_plaintext * std_traces
        result = (num / row_number) / denum
        pearson_array_result2[i] = result

    pd.DataFrame(pearson_array_result).to_csv(os.path.join(directory, f'./attack/result/pearson_array_result.csv'))
    pd.DataFrame(pearson_array_result2).to_csv(os.path.join(directory, f'./attack/result/pearson_array_result2.csv'))


def HW_calculator(n):
    return bin(n).count("1")
