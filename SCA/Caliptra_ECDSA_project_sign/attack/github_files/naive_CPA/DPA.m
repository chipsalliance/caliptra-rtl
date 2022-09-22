

close all;
clear all;
correct_key=[209,  21,  250,  169,  202,  239,  38,  138,  226,  64,  13,  201,  183,  100,  13,  167];
key_byte=2;
b_end             = (key_byte*2);
b_start           = b_end - 1;
ind               = mod(key_byte-1, 16);
ind               = mod(key_byte -1 + (ind * -4), 16) + 1;
fx_trace_name='C:/Users/ekarabu/Desktop/parallel_AES/captured_data/one_unrolled/powertrace_fixed_';
rd_trace_name='C:/Users/ekarabu/Desktop/parallel_AES/captured_data/one_unrolled/powertrace_rnd_';
traces= zeros(1001000,2501);
cnt=0;
for i=1:4
    str = num2str(i-1)
    str = strcat(str,'.csv');
    sub_traces=csvread(strcat(rd_trace_name,str));
    [m,n]=size(sub_traces)
    traces((cnt+1):(cnt+m), :) = sub_traces;
    cnt=cnt+m;
end
%cnt=cnt-m;
sub_traces=traces((1:cnt),:);
traces=sub_traces;
clear sub_traces

cipher_array=csvread('C:/Users/ekarabu/Desktop/parallel_AES/captured_data/one_unrolled/random_plaintext.csv');
cipher_array=cipher_array((1:cnt),:);
cipher_array2=csvread('C:/Users/ekarabu/Desktop/parallel_AES/captured_data/one_unrolled/random_plaintext2.csv');



plot(traces(1,:));

isbox = [82,9,106,213,48,54,165,56,191,64,163,158,129,243,215,251,124,227,57,130,155,47,255,135,52,142,67,68,196,222,233,203,84,123,148,50,166,194,35,61,238,76,149,11,66,250,195,78,8,46,161,102,40,217,36,178,118,91,162,73,109,139,209,37,114,248,246,100,134,104,152,22,212,164,92,204,93,101,182,146,108,112,72,80,253,237,185,218,94,21,70,87,167,141,157,132,144,216,171,0,140,188,211,10,247,228,88,5,184,179,69,6,208,44,30,143,202,63,15,2,193,175,189,3,1,19,138,107,58,145,17,65,79,103,220,234,151,242,207,206,240,180,230,115,150,172,116,34,231,173,53,133,226,249,55,232,28,117,223,110,71,241,26,113,29,41,197,137,111,183,98,14,170,24,190,27,252,86,62,75,198,210,121,32,154,219,192,254,120,205,90,244,31,221,168,51,136,7,199,49,177,18,16,89,39,128,236,95,96,81,127,169,25,181,74,13,45,229,122,159,147,201,156,239,160,224,59,77,174,42,245,176,200,235,187,60,131,83,153,97,23,43,4,126,186,119,214,38,225,105,20,99,85,33,12,125];
[row col]=size(traces);


plot(traces(30,:));
clear pearson_array_result
clear pearson_eval


HW_matrix= zeros(row,256);

for i=1:row
    plain_target=cipher_array(i,ind);
    plain_target2=cipher_array2(i,ind);
    for j=1:256
        target1=isbox(bitxor(plain_target, j-1) + 1);
        target2=isbox(bitxor(plain_target2, j-1) + 1);
        key_hyp_result=dec2bin(bitxor(target1,target2));
        HW_matrix(i,j)=length(find(key_hyp_result=='1'));
    end
end


var_realmeas=traces-mean(traces);
pearson_array_result=zeros(256,col);

for i=1:256
        res_array=HW_matrix(:,i);
        var_res=res_array-mean(res_array);        
        pearson_cor=((var_res'*var_realmeas)/row)./(std(res_array)*std(traces));
        pearson_array_result(i,:)=pearson_cor;
end

figure();
plot(pearson_array_result');

[max_val,max_ind]=max(max(pearson_array_result));
[sort_max_val,sort_max_ind]=sort(pearson_array_result(:,max_ind));
[min_val,min_ind]=min(min(pearson_array_result));
[sort_min_val,sort_min_ind]=sort(pearson_array_result(:,min_ind));

figure();
hold all;
plot(pearson_array_result(sort_max_ind(1),:));
plot(pearson_array_result(sort_min_ind(256),:));

cnt=1;
for i=4:1000:row
    for j=1:256
        res_array=HW_matrix(1:i,j);        
        realmes_array=traces((1:i),1:2000);
        
        var_res=res_array-mean(res_array);
        var_realmeas=realmes_array-mean(realmes_array);
        
        pearson_cor=((var_res'*var_realmeas)/i)./(std(res_array)*std(realmes_array));
        pearson_eval(j,cnt)=max(abs(pearson_cor));
    end
    [sort_max_val,sort_max_ind]=sort(abs(pearson_eval(:,cnt)));
    rank(cnt,1)= 256-find(sort_max_ind==correct_key(1,ind));
    cnt=cnt+1;
end

figure();
plot(pearson_eval','Color',[0.5 0.5 0.5])
hold on
plot(pearson_eval(correct_key(1,ind),:)','r')
figure();
plot(rank)

figure();
plot(pearson_array_result','Color',[0.5 0.5 0.5])
hold on
plot(pearson_array_result(correct_key(1,ind),:)','r')
    