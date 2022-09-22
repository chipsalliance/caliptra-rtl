clear all
clc
datas ={'one_unrolled' 'one_unrolled_1' 'two_unrolled_00' 'two_unrolled_10'}
for ll=1:4
    
	key=9;
	original_str='C:/Users/ekarabu/Desktop/parallel_AES/captured_data/results/full_key/';
    original_str = strcat(original_str,string(datas(1,ll)));
    original_str = strcat(original_str,'/');
	str1 = strcat(original_str,'matlab.mat');
	load(str1);
	[m n]=size(rank);
	
	for i=1:m
		for k=1:16
			if rank(i,k)~=0
				key=k;
			end
		end
	end
	
	figure();
	for i=1:16
		if i~=key
			plot(rank(:,i),'Color',[0.5 0.5 0.5])
		else
			plot(rank(:,i),'r','LineWidth',1.5)
		end
		hold on
	end
	Legend=cell(16,1);
	for iter=1:16
	Legend{iter}=strcat('Key-byte ', num2str(iter));
	end
	legend(Legend)
	clear Legend
	str1 = strcat(original_str,'CPA_rank.png');
	saveas(gcf,str1)
	
	figure();
	plot(squeeze(pearson_eval(key,:,:))','Color',[0.5 0.5 0.5])
	hold on
	plot(squeeze(pearson_eval(key,correct_key(1,key),:))','r','LineWidth',1.5)
    if ll==2
        ylim([0 0.045])
    else
        ylim([0 0.02])
    end
	str1 = strcat(original_str,'CPA_ev.png');
	saveas(gcf,str1)
	
	var_realmeas=traces-mean(traces);
	pearson_array_result=zeros(256,col);
	kkk=squeeze(HW_matrix(key,:,:));
	
	for i=1:256
			res_array=kkk(:,i);
			var_res=res_array-mean(res_array);        
			pearson_cor=((var_res'*var_realmeas)/row)./(std(res_array)*std(traces));
			pearson_array_result(i,:)=pearson_cor;
	end
	figure();
	plot(pearson_array_result','Color',[0.5 0.5 0.5])
	hold on
	plot(pearson_array_result(correct_key(1,key),:)','r','LineWidth',1.5)
	str1 = strcat(original_str,'CPA.png');
	saveas(gcf,str1)

end
