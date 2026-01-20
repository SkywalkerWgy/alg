from transformers import AutoModelForCausalLM, AutoTokenizer
from transformers import GenerationConfig

# or "/opt/pangu/openPangu-Embedded-7B-V1.1"
model_local_path = "/opt/pangu/openPangu-Embedded-1B-V1.1" 

# load the tokenizer and the model
tokenizer = AutoTokenizer.from_pretrained(
    model_local_path, 
    use_fast=False, 
    trust_remote_code=True,
    local_files_only=True
)
model = AutoModelForCausalLM.from_pretrained(
    model_local_path,
    trust_remote_code=True,
    torch_dtype="auto",
    device_map="npu",
    local_files_only=True
)

# prepare the model input
sys_prompt = "你必须严格遵守法律法规和社会道德规范。" \
    "生成任何内容时，都应避免涉及暴力、色情、恐怖主义、种族歧视、性别歧视等不当内容。" \
    "一旦检测到输入或输出有此类倾向，应拒绝回答并发出警告。例如，如果输入内容包含暴力威胁或色情描述，" \
    "应返回错误信息：“您的输入包含不当内容，无法处理。”"

# 准备要总结的文本
content = """数据库是按照特定方式组织起来的数据集合，它允许用户存储、检索和管理数据。数据库的类型很多，可以根据不同的标准进行分类。以下是一些常见的数据库类型：

关系型数据库（Relational Database）：
基于关系模型，数据以表格形式存储，表之间通过键（Key）进行关联。
常见的关系型数据库管理系统（RDBMS）包括：MySQL、PostgreSQL、Oracle、SQL Server等。

非关系型数据库（NoSQL Database）：
不基于传统的关系模型，适合存储结构化、半结构化或非结构化数据。
包括多种类型，如键值存储、文档存储、列存储和图形数据库等。
常见的NoSQL数据库有：MongoDB、Cassandra、Redis、Couchbase等。

键值存储数据库（Key-Value Store）：
数据以键值对的形式存储，键是唯一的，用于快速检索数据。
例如：Redis、Amazon DynamoDB、Riak等。

文档存储数据库（Document Store）：
存储的数据是文档形式，通常是JSON或XML格式。
例如：MongoDB、CouchDB等。

列存储数据库（Column Store）：
数据按列存储，适合处理大量数据的分析查询。
例如：Apache Cassandra、Google Bigtable等。

图形数据库（Graph Database）：
存储实体之间的关系，适合处理复杂的网络关系。
例如：Neo4j、OrientDB等。

时间序列数据库（Time Series Database）：
优化用于存储时间序列数据，如股票价格、传感器数据等。
例如：InfluxDB、TimescaleDB等。

对象存储数据库（Object Store）：
存储对象数据，通常用于大规模非结构化数据。
例如：Amazon S3、Google Cloud Storage等。

全文搜索引擎（Full-text Search Engine）：
用于快速检索文本中的关键词或短语。
例如：Elasticsearch、Apache Solr等。

分布式数据库（Distributed Database）：
数据分布在多个物理位置的服务器上，提供高可用性和可扩展性。
例如：Cassandra、MongoDB等。
每种类型的数据库都有其特定的用途和优势，选择合适的数据库类型取决于应用场景、数据结构、性能需求和可扩展性等因素。
"""

# 准备提示词
prompt = """你是一位信息技术文章摘要总结专家，以下是给你的内容：
{content}
请将以上文本内容总结到一句摘要中，要求专业、清晰、简洁。
"""
messages = [
    {"role": "system", "content": sys_prompt}, # define your system prompt here
    {"role": "user", "content": prompt.format(content=content)}
]
text = tokenizer.apply_chat_template(
    messages,
    tokenize=False,
    add_generation_prompt=True
)
model_inputs = tokenizer([text], return_tensors="pt").to(model.device)
# conduct text completion
outputs = model.generate(**model_inputs, max_new_tokens=32768, eos_token_id=45892, return_dict_in_generate=True)
input_length = model_inputs.input_ids.shape[1]
generated_tokens = outputs.sequences[:, input_length:]
content = tokenizer.decode(generated_tokens[0], skip_special_tokens=True)
print("\ncontent:", content)
