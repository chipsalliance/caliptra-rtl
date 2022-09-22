

close all;
clear all;
correct_key=[209,  21,  250,  169,  202,  239,  38,  138,  226,  64,  13,  201,  183,  100,  13,  167];

inval=1000

randomization=csvread('C:/Users/ekarabu/Desktop/parallel_AES/captured_data/two_unrolled_00/randomization_order.csv');
fx_trace_name='C:/Users/ekarabu/Desktop/parallel_AES/captured_data/two_unrolled_00/powertrace_fixed_';
rd_trace_name='C:/Users/ekarabu/Desktop/parallel_AES/captured_data/two_unrolled_00/powertrace_rnd_';
traces= zeros(1001000,2501);
cnt=0;
for i=1:8
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

cipher_array=csvread('C:/Users/ekarabu/Desktop/parallel_AES/captured_data/two_unrolled_00/random_plaintext.csv');
cipher_array=cipher_array((1:cnt),:);
cipher_array2=csvread('C:/Users/ekarabu/Desktop/parallel_AES/captured_data/two_unrolled_00/random_plaintext2.csv');

isbox = [82,9,106,213,48,54,165,56,191,64,163,158,129,243,215,251,124,227,57,130,155,47,255,135,52,142,67,68,196,222,233,203,84,123,148,50,166,194,35,61,238,76,149,11,66,250,195,78,8,46,161,102,40,217,36,178,118,91,162,73,109,139,209,37,114,248,246,100,134,104,152,22,212,164,92,204,93,101,182,146,108,112,72,80,253,237,185,218,94,21,70,87,167,141,157,132,144,216,171,0,140,188,211,10,247,228,88,5,184,179,69,6,208,44,30,143,202,63,15,2,193,175,189,3,1,19,138,107,58,145,17,65,79,103,220,234,151,242,207,206,240,180,230,115,150,172,116,34,231,173,53,133,226,249,55,232,28,117,223,110,71,241,26,113,29,41,197,137,111,183,98,14,170,24,190,27,252,86,62,75,198,210,121,32,154,219,192,254,120,205,90,244,31,221,168,51,136,7,199,49,177,18,16,89,39,128,236,95,96,81,127,169,25,181,74,13,45,229,122,159,147,201,156,239,160,224,59,77,174,42,245,176,200,235,187,60,131,83,153,97,23,43,4,126,186,119,214,38,225,105,20,99,85,33,12,125];
[row col]=size(traces);


clear pearson_array_result
clear pearson_eval

f = waitbar(0, 'Starting');
jump=1;
HW_matrix= zeros(16,row,256);
size_2=ceil(row/inval);
pearson_eval= zeros(16,256,size_2);

	
	

cnt=1;
std_trace= zeros(1,col);

for i=1:row
    for key_byte=1:16
        b_end             = (key_byte*2);
        b_start           = b_end - 1;
        ind               = mod(key_byte-1, 16);
        ind               = mod(key_byte -1 + (ind * -4), 16) + 1;
        plain_target=cipher_array(i,ind);
        plain_target2=cipher_array2(i,ind);
        HW_matrix(ind,i,:)=unrolled_HD_leakage(plain_target,plain_target2);
    end
	waitbar(i/row, f, sprintf('Key %d Progress: %d %%',key_byte, floor(i/row*100)));
	if (i ==1)
			mean_trace= mean(traces(1,:));
			var_trace=var(traces(i,:));
	else
			sub_trace=traces(i,:);
			old_mean=mean_trace;
			mean_trace = mean_trace+(sub_trace-mean_trace)/i;
			v1=sub_trace-old_mean;
			v2=sub_trace-mean_trace;;
			var_trace=var_trace+v1.*v2;
			std_trace=sqrt(var_trace/i);
	end
	if (mod(i, inval)==0 && i ~=0)
		var_realmeas=traces(1:i,:)-mean(traces(1:i,:));
        for key_byte=1:16
            b_end             = (key_byte*2);
            b_start           = b_end - 1;
            ind               = mod(key_byte-1, 16);
            ind               = mod(key_byte -1 + (ind * -4), 16) + 1;
            res_array=squeeze(HW_matrix(ind,1:i,:));
            var_res=res_array-mean(res_array);
            std_res=std(res_array);
            for j=1:256              
                pearson_cor=((var_res(:,j)'*var_realmeas)/i)./(std_res(1,j)*std_trace);
                pearson_eval(ind,j,cnt)=max(abs(pearson_cor));
            end
            pearson_cor=squeeze(pearson_eval(ind,:,cnt));
            [sort_max_val,sort_max_ind]=sort((pearson_cor(1,:)));
            rank(cnt,ind)= 256-find(sort_max_ind==correct_key(1,ind));
        end
        cnt=cnt+1;
    end
end





figure();
plot(squeeze(pearson_eval(ind,:,:))','Color',[0.5 0.5 0.5])
figure();
plot(rank)

figure();
plot(pearson_array_result','Color',[0.5 0.5 0.5])
hold on
plot(pearson_array_result(correct_key(1,key_byte),:)','r')
    