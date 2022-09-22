clear all
clc
pearson_corr= csvread('C:\Users\t-ekarabulut\OneDrive - Microsoft\Caliptra_ECDSA_project_sign\attack\result\pearson_array_result.csv');
close all
pearson_corr(1,:)= [];
pearson_corr(:,1)= [];
figure();
plot(pearson_corr');
figure();
plot(pearson_corr(1,:)')

[max_val,max_ind]=max(max(pearson_corr));
[sort_max_val,sort_max_ind]=sort(pearson_corr(:,max_ind));
[min_val,min_ind]=min(min(pearson_corr));
[sort_min_val,sort_min_ind]=sort(pearson_corr(:,min_ind));
pearson_corr2= csvread('C:\Users\t-ekarabulut\OneDrive - Microsoft\Caliptra_ECDSA_project_sign\attack\result\pearson_array_result2.csv');
close all
pearson_corr2(1,:)= [];
pearson_corr2(:,1)= [];
figure();
plot(pearson_corr2');
figure();
plot(pearson_corr2(1,:)')

[max_val,max_ind]=max(max(pearson_corr2));
[sort_max_val,sort_max_ind]=sort(pearson_corr2(:,max_ind));
[min_val,min_ind]=min(min(pearson_corr2));
[sort_min_val,sort_min_ind]=sort(pearson_corr2(:,min_ind));


%trace= csvread('C:\Users\t-ekarabulut\OneDrive - Microsoft\Caliptra_ECDSA_project_sign\data\powertrace_rnd_0.csv');
%figure();
%plot(trace(20:50,:)')