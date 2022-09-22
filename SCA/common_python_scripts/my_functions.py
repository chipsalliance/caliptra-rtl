import scipy.interpolate as spi
import numpy as np
import pandas as pd
import matplotlib.pyplot as plt
import csv
import os
from itertools import zip_longest


def get_equation(x,y, degree = 1):
    coefs, res, _, _, _ = np.polyfit(x,y,degree, full = True)
    ffit = np.poly1d(coefs)
    print (ffit)
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

    predict = get_equation(count_x_axis,count_45)
    # np.arange(start, end + step, step)
    x_new = np.arange((cnt+1)*100, predicted_point+100, 100)

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
    a=predict(predicted_point)
    plt.plot(predicted_point, predict(predicted_point), 'ro')
    plt.savefig(os.path.join(directory, f'./attack/result/1st-order-tvla-evolution.png'))
    plt.close()

    data = [count_x_axis, count_45, max_t_values]
    export_data = zip_longest(*data, fillvalue='')
    with open(os.path.join(directory, f'./attack/result/raw_data.csv'), 'w', encoding="ISO-8859-1", newline='') as file:
        write = csv.writer(file)
        write.writerow(("# traces ","# t > 4.5 t", "max"))
        write.writerows(export_data)
